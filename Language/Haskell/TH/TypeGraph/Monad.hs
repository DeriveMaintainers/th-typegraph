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
    ( vertex
    , vertices
    , typeGraphEdges
    , simpleEdges
    , simpleVertex
    ) where

#if __GLASGOW_HASKELL__ < 709
import Data.Monoid (mempty)
#endif
import Control.Lens -- (makeLenses, view)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (execStateT, modify, StateT)
import Data.Default (Default(def))
import Data.List as List (intercalate, map)
import Data.Map as Map ((!), findWithDefault, keys, lookup, map, mapKeys, mapWithKey, alter)
import Data.Maybe (fromMaybe)
import Data.Set as Set (delete, empty, insert, map, null, Set, singleton, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.TypeGraph.Core (Field, pprint')
import Language.Haskell.TH.TypeGraph.Expand (E(E))
import Language.Haskell.TH.TypeGraph.Graph (cutVertex, GraphEdges)
import Language.Haskell.TH.TypeGraph.Hints (HasVertexHints(hasVertexHints), VertexHint(..))
import Language.Haskell.TH.TypeGraph.Info (TypeGraphInfo, expanded, fields, hints, infoMap, synonyms, typeSet)
import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex(..), etype, field)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()

-- | Build a vertex from the given 'Type' and optional 'Field'.
vertex :: MonadReader (TypeGraphInfo hint) m => Maybe Field -> Type -> m TypeGraphVertex
vertex fld typ = do
  em <- view expanded
  let etyp = fromMaybe (error $ "vertex - unknown type: " ++ pprint' typ ++ "\n" ++
                                intercalate "\n  " ("known:" : List.map pprint' (Map.keys em)))
                       (Map.lookup typ em)
  maybe (typeVertex etyp) (fieldVertex etyp) fld
    where
      typeVertex :: MonadReader (TypeGraphInfo hint) m => E Type -> m TypeGraphVertex
      typeVertex etyp = do
        sm <- view synonyms
        return $ TypeGraphVertex {_field = Nothing, _syns = Map.findWithDefault Set.empty etyp sm, _etype = etyp}
      fieldVertex :: MonadReader (TypeGraphInfo hint) m => E Type -> Field -> m TypeGraphVertex
      fieldVertex etyp fld' = typeVertex etyp >>= \v -> return $ v {_field = Just fld'}

-- | Build the vertices that involve a particular type - if the field
-- is specified it return s singleton, otherwise it returns a set
-- containing a vertex one for the type on its own, and one for each
-- field containing that type.
vertices :: MonadReader (TypeGraphInfo hint) m => Maybe Field -> Type -> m (Set TypeGraphVertex)
vertices fld typ = do
  fm <- view fields
  v <- vertex Nothing typ
  case fld of
    Nothing -> let fs = Map.findWithDefault Set.empty (view etype v) fm
                   vs = Set.map (\fld' -> set field (Just fld') v) fs in
               return $ Set.insert v vs
    Just _ -> return $ singleton $ set field fld v

-- | Start with the type graph on the known types with no field
-- information, and build a new graph which incorporates the
-- information from the vertex hints.  This means splitting the nodes
-- according to record fields, because hints can refer to particular
-- fields of a record.
typeGraphEdges :: forall m hint. (DsMonad m, Default hint, HasVertexHints hint, MonadReader (TypeGraphInfo hint) m) => m (GraphEdges hint TypeGraphVertex)
typeGraphEdges = do
  findEdges >>= execStateT (view hints >>= mapM (\(fld, typ, hint) -> mapM_ (doHint fld typ) (hasVertexHints hint)))
    where
      doHint :: Maybe Field -> Type -> VertexHint -> StateT (GraphEdges hint TypeGraphVertex) m ()
      doHint fld typ Sink = do
        vertices fld typ >>= mapM_ (modify . Map.alter (alterFn (const Set.empty))) . Set.toList
      doHint _ _ Normal = return ()
      doHint fld typ Hidden = do
        vertices fld typ >>= mapM_ (modify . cutVertex) . Set.toList
      doHint fld typ (Divert typ') = do
        v' <- vertex Nothing typ'
        vertices fld typ >>= mapM_ (modify . Map.alter (alterFn (const (singleton v')))) . Set.toList
      doHint fld typ (Extra typ') = do
        v' <- vertex Nothing typ'
        vertices fld typ >>= mapM_ (modify . Map.alter (alterFn (Set.insert v'))) . Set.toList

alterFn :: Default hint => (Set TypeGraphVertex -> Set TypeGraphVertex) -> Maybe (hint, Set TypeGraphVertex) -> Maybe (hint, Set TypeGraphVertex)
alterFn setf (Just (hint, s)) = Just (hint, setf s)
alterFn setf Nothing | Set.null (setf Set.empty) = Nothing
alterFn setf Nothing = Just (def, setf Set.empty)

-- | Given the discovered set of types and maps of type synonyms and
-- fields, build and return the GraphEdges relation on TypeGraphVertex.
-- This is not a recursive function, it stops when it reaches the field
-- types.
findEdges :: forall hint m. (Default hint, MonadReader (TypeGraphInfo hint) m) =>
             m (GraphEdges hint TypeGraphVertex)
findEdges = do
  execStateT (view typeSet >>= \ts -> mapM_ doType (Set.toList ts)) mempty
    where
      doType :: Type -> StateT (GraphEdges hint TypeGraphVertex) m ()
      doType typ = do
        em <- view expanded
        vs <- vertices Nothing typ
        mapM_ node (Set.toList vs)
        case em ! typ of
          E (ConT tname) -> view infoMap >>= \ mp -> doInfo vs (mp ! tname)
          E (AppT typ1 typ2) -> do
            v1 <- vertex Nothing typ1
            v2 <- vertex Nothing typ2
            mapM_ (flip edge v1) (Set.toList vs)
            mapM_ (flip edge v2) (Set.toList vs)
            doType typ1
            doType typ2
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
      doField ::  Set TypeGraphVertex ->Name -> Name -> Either Int Name -> Type -> StateT (GraphEdges hint TypeGraphVertex) m ()
      doField vs tname cname fld ftyp = do
        v2 <- vertex (Just (tname, cname, fld)) ftyp
        mapM_ (flip edge v2) (Set.toList vs)
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
simpleEdges :: GraphEdges hint TypeGraphVertex -> GraphEdges hint TypeGraphVertex
simpleEdges = Map.mapWithKey (\v (n, s) -> (n, Set.delete v s)) .    -- delete any self edges
              Map.mapKeys simpleVertex .               -- simplify each vertex
              Map.map (over _2 (Set.map simpleVertex)) -- simplify the out edges

simpleVertex :: TypeGraphVertex -> TypeGraphVertex
simpleVertex v = v {_field = Nothing}
