-- | Operations using @MonadReader (TypeGraphInfo hint)@.

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.TH.TypeGraph.Monad
    ( fieldVertices
    , allVertices
    , vertex
    , typeVertex
    , fieldVertex
    , typeGraphEdges
    , simpleEdges
    , simpleVertex
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>))
import Data.Monoid (mempty)
#endif
import Control.Lens -- (makeLenses, view)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (execStateT, modify, StateT)
import Data.Default (Default(def))
import Data.Foldable
import Data.List as List (map)
import Data.Map as Map ((!), alter, findWithDefault, map, mapKeysWith, mapWithKey)
import Data.Monoid (Monoid, (<>))
import Data.Set as Set (delete, empty, insert, map, Set, singleton, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.TypeGraph.Core (Field)
import Language.Haskell.TH.TypeGraph.Expand (E(E), expandType)
import Language.Haskell.TH.TypeGraph.Graph (GraphEdges)
import Language.Haskell.TH.TypeGraph.Info (TypeGraphInfo, fields, infoMap, synonyms, typeSet)
import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex(..), etype, field)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Prelude hiding (foldr, mapM_, null)

allVertices :: (Functor m, DsMonad m, MonadReader (TypeGraphInfo hint) m) =>
               Maybe Field -> E Type -> m (Set TypeGraphVertex)
allVertices (Just fld) etyp = singleton <$> vertex (Just fld) etyp
allVertices Nothing etyp = vertex Nothing etyp >>= \v -> fieldVertices v >>= \vs -> return $ Set.insert v vs

-- | Build the vertices that involve a particular type - if the field
-- is specified it return s singleton, otherwise it returns a set
-- containing a vertex one for the type on its own, and one for each
-- field containing that type.
fieldVertices :: MonadReader (TypeGraphInfo hint) m => TypeGraphVertex -> m (Set TypeGraphVertex)
fieldVertices v = do
  fm <- view fields
  let fs = Map.findWithDefault Set.empty (view etype v) fm
  return $ Set.map (\fld' -> set field (Just fld') v) fs

-- | Build a vertex from the given 'Type' and optional 'Field'.
vertex :: forall m hint. (DsMonad m, MonadReader (TypeGraphInfo hint) m) => Maybe Field -> E Type -> m TypeGraphVertex
vertex fld etyp = maybe (typeVertex etyp) (fieldVertex etyp) fld

-- | Build a non-field vertex
typeVertex :: MonadReader (TypeGraphInfo hint) m => E Type -> m TypeGraphVertex
typeVertex etyp = do
  sm <- view synonyms
  return $ TypeGraphVertex {_field = Nothing, _syns = Map.findWithDefault Set.empty etyp sm, _etype = etyp}

-- | Build a vertex associated with a field
fieldVertex :: MonadReader (TypeGraphInfo hint) m => E Type -> Field -> m TypeGraphVertex
fieldVertex etyp fld' = typeVertex etyp >>= \v -> return $ v {_field = Just fld'}

-- | Given the discovered set of types and maps of type synonyms and
-- fields, build and return the GraphEdges relation on TypeGraphVertex.
-- This is not a recursive function, it stops when it reaches the field
-- types.
typeGraphEdges :: forall hint m. (DsMonad m, Functor m, Default hint, MonadReader (TypeGraphInfo hint) m) =>
                  m (GraphEdges hint TypeGraphVertex)
typeGraphEdges = do
  execStateT (view typeSet >>= \ts -> mapM_ (\t -> expandType t >>= doType) ts) mempty
    where
      doType :: E Type -> StateT (GraphEdges hint TypeGraphVertex) m ()
      doType typ = do
        vs <- allVertices Nothing typ
        mapM_ node vs
        case typ of
          E (ConT tname) -> view infoMap >>= \ mp -> doInfo vs (mp ! tname)
          E (AppT typ1 typ2) -> do
            v1 <- vertex Nothing (E typ1)
            v2 <- vertex Nothing (E typ2)
            mapM_ (flip edge v1) vs
            mapM_ (flip edge v2) vs
            doType (E typ1)
            doType (E typ2)
          _ -> return ()

      doInfo :: Set TypeGraphVertex -> Info -> StateT (GraphEdges hint TypeGraphVertex) m ()
      doInfo vs (TyConI dec) = doDec vs dec
      -- doInfo vs (PrimTyConI tname _ _) = return ()
      doInfo _ _ = return ()

      doDec :: Set TypeGraphVertex -> Dec -> StateT (GraphEdges hint TypeGraphVertex) m ()
      doDec _ (TySynD _ _ _) = return () -- This type will be in typeSet
      doDec vs (NewtypeD _ tname _ constr _) = doCon vs tname constr
      doDec vs (DataD _ tname _ constrs _) = mapM_ (doCon vs tname) constrs
      doDec _ _ = return ()

      doCon :: Set TypeGraphVertex -> Name -> Con -> StateT (GraphEdges hint TypeGraphVertex) m ()
      doCon vs tname (ForallC _ _ con) = doCon vs tname con
      doCon vs tname (NormalC cname flds) = mapM_ (uncurry (doField vs tname cname)) (List.map (\ (n, (_, ftype)) -> (Left n, ftype)) (zip [1..] flds))
      doCon vs tname (RecC cname flds) = mapM_ (uncurry (doField vs tname cname)) (List.map (\ (fname, _, ftype) -> (Right fname, ftype)) flds)
      doCon vs tname (InfixC (_, lhs) cname (_, rhs)) = doField vs tname cname (Left 1) lhs >> doField vs tname cname (Left 2) rhs

      -- Connect the vertex for this record type to one particular field vertex
      doField ::  DsMonad m => Set TypeGraphVertex -> Name -> Name -> Either Int Name -> Type -> StateT (GraphEdges hint TypeGraphVertex) m ()
      doField vs tname cname fld ftyp = do
        v2 <- expandType ftyp >>= vertex (Just (tname, cname, fld))
        v3 <- expandType ftyp >>= vertex Nothing
        edge v2 v3
        mapM_ (flip edge v2) vs
        -- Here's where we don't recurse, see?
        -- doVertex v2

      node :: TypeGraphVertex -> StateT (GraphEdges hint TypeGraphVertex) m ()
      node v = modify (Map.alter (Just . maybe (def, Set.empty) id) v)

      edge :: TypeGraphVertex -> TypeGraphVertex -> StateT (GraphEdges hint TypeGraphVertex) m ()
      edge v1 v2 = modify f >> node v2
          where f :: GraphEdges hint TypeGraphVertex -> GraphEdges hint TypeGraphVertex
                f = Map.alter g v1
                g :: (Maybe (hint, Set TypeGraphVertex) -> Maybe (hint, Set TypeGraphVertex))
                g = Just . maybe (def, singleton v2) (over _2 (Set.insert v2))

-- | Simplify a graph by throwing away the field information in each
-- node.  This means the nodes only contain the fully expanded Type
-- value (and any type synonyms.)
simpleEdges :: Monoid hint => GraphEdges hint TypeGraphVertex -> GraphEdges hint TypeGraphVertex
simpleEdges = Map.mapWithKey (\v (n, s) -> (n, Set.delete v s)) .    -- delete any self edges
              Map.mapKeysWith combine simpleVertex .   -- simplify each vertex
              Map.map (over _2 (Set.map simpleVertex)) -- simplify the out edges
    where
      combine (n1, s1) (n2, s2) = (n1 <> n2, Set.union s1 s2)

simpleVertex :: TypeGraphVertex -> TypeGraphVertex
simpleVertex v = v {_field = Nothing}
