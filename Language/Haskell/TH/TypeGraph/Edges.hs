-- | Operations involving the edges of the graph (before it is a graph.)

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
module Language.Haskell.TH.TypeGraph.Edges
    ( GraphEdges
    , typeGraphEdges
    , cut
    , cutM
    , cutEdges
    , isolate
    , isolateM
    , dissolve
    , dissolveM
    , simpleEdges
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
import Data.Map as Map ((!), alter)
import Data.Set as Set (empty, insert, Set, singleton)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.TypeGraph.Expand (E(E), expandType)
import Language.Haskell.TH.TypeGraph.Info (TypeInfo, infoMap, typeSet, allVertices, vertex)
import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Prelude hiding (foldr, mapM_, null)

import Control.Monad (filterM)
import Data.List as List (intercalate)
import Data.Map as Map (Map, elems, filterWithKey, keys, map, mapKeysWith, mapWithKey, partitionWithKey)
import qualified Data.Map as Map (toList)
import Data.Monoid ((<>))
import Data.Set as Set (delete, filter, map, member, fromList, union, unions)
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.TypeGraph.Shape (pprint')
import Language.Haskell.TH.TypeGraph.Vertex (simpleVertex)
import Prelude hiding (foldr)

type GraphEdges node key = Map key (node, Set key)

-- | Given the discovered set of types and maps of type synonyms and
-- fields, build and return the GraphEdges relation on TypeGraphVertex.
-- This is not a recursive function, it stops when it reaches the field
-- types.
typeGraphEdges :: forall node m. (DsMonad m, Functor m, Default node, MonadReader TypeInfo m) =>
                  m (GraphEdges node TypeGraphVertex)
typeGraphEdges = do
  execStateT (view typeSet >>= mapM_ (\t -> expandType t >>= doType)) mempty
    where
      doType :: E Type -> StateT (GraphEdges node TypeGraphVertex) m ()
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

      doInfo :: Set TypeGraphVertex -> Info -> StateT (GraphEdges node TypeGraphVertex) m ()
      doInfo vs (TyConI dec) = doDec vs dec
      -- doInfo vs (PrimTyConI tname _ _) = return ()
      doInfo _ _ = return ()

      doDec :: Set TypeGraphVertex -> Dec -> StateT (GraphEdges node TypeGraphVertex) m ()
      doDec _ (TySynD _ _ _) = return () -- This type will be in typeSet
      doDec vs (NewtypeD _ tname _ constr _) = doCon vs tname constr
      doDec vs (DataD _ tname _ constrs _) = mapM_ (doCon vs tname) constrs
      doDec _ _ = return ()

      doCon :: Set TypeGraphVertex -> Name -> Con -> StateT (GraphEdges node TypeGraphVertex) m ()
      doCon vs tname (ForallC _ _ con) = doCon vs tname con
      doCon vs tname (NormalC cname flds) = mapM_ (uncurry (doField vs tname cname)) (List.map (\ (n, (_, ftype)) -> (Left n, ftype)) (zip [1..] flds))
      doCon vs tname (RecC cname flds) = mapM_ (uncurry (doField vs tname cname)) (List.map (\ (fname, _, ftype) -> (Right fname, ftype)) flds)
      doCon vs tname (InfixC (_, lhs) cname (_, rhs)) = doField vs tname cname (Left 1) lhs >> doField vs tname cname (Left 2) rhs

      -- Connect the vertex for this record type to one particular field vertex
      doField ::  DsMonad m => Set TypeGraphVertex -> Name -> Name -> Either Int Name -> Type -> StateT (GraphEdges node TypeGraphVertex) m ()
      doField vs tname cname fld ftyp = do
        v2 <- expandType ftyp >>= vertex (Just (tname, cname, fld))
        v3 <- expandType ftyp >>= vertex Nothing
        edge v2 v3
        mapM_ (flip edge v2) vs
        -- Here's where we don't recurse, see?
        -- doVertex v2

      node :: TypeGraphVertex -> StateT (GraphEdges node TypeGraphVertex) m ()
      -- node v = pass (return ((), (Map.alter (Just . maybe (def, Set.empty) id) v)))
      node v = modify (Map.alter (Just . maybe (def, Set.empty) id) v)

      edge :: TypeGraphVertex -> TypeGraphVertex -> StateT (GraphEdges node TypeGraphVertex) m ()
      edge v1 v2 = node v2 >> modify f
          where f :: GraphEdges node TypeGraphVertex -> GraphEdges node TypeGraphVertex
                f = Map.alter g v1
                g :: (Maybe (node, Set TypeGraphVertex) -> Maybe (node, Set TypeGraphVertex))
                g = Just . maybe (def, singleton v2) (over _2 (Set.insert v2))

instance Ppr key => Ppr (GraphEdges node key) where
    ppr x =
        ptext $ intercalate "\n  " $
          "edges:" : (List.map
                       (\(k, (_, ks)) -> intercalate "\n    " ((pprint' k ++ " ->" ++ if null ks then " []" else "") : List.map pprint' (toList ks)))
                       (Map.toList x))

-- | Isolate and remove some nodes
cut :: (Eq a, Ord a) => Set a -> GraphEdges node a -> GraphEdges node a
cut victims edges = Map.filterWithKey (\v _ -> not (Set.member v victims)) (isolate victims edges)

-- | Monadic predicate version of 'cut'.
cutM :: (Functor m, Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges node a -> m (GraphEdges node a)
cutM victim edges = do
  victims <- Set.fromList <$> filterM victim (Map.keys edges)
  return $ cut victims edges

cutEdges :: (Eq a, Ord a) => (a -> a -> Bool) -> GraphEdges node a -> (GraphEdges node a)
cutEdges p edges = Map.mapWithKey (\key (hint, gkeys) -> (hint, Set.filter (\gkey -> p key gkey) gkeys)) edges

-- | Remove all the in- and out-edges of some nodes
isolate :: (Eq a, Ord a) => Set a -> GraphEdges node a -> GraphEdges node a
isolate victims edges = cutEdges (\ a b -> Set.member a victims || Set.member b victims) edges
#if 0
    edges''
    where
      edges' = Map.mapWithKey (\v (h, s) -> (h, if Set.member v victims then Set.empty else s)) edges -- Remove the out-edges
      edges'' = Map.map (over _2 (Set.filter (not . (`Set.member` victims)))) edges' -- Remove the in-edges
#endif

-- | Monadic predicate version of 'isolate'.
isolateM :: (Functor m, Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges node a -> m (GraphEdges node a)
isolateM victim edges = do
  victims <- Set.fromList <$> filterM victim (Map.keys edges)
  return $ isolate victims edges

-- | Remove some nodes and extend each of their in-edges to each of
-- their out-edges
dissolve :: (Eq a, Ord a) => Set a -> GraphEdges node a -> GraphEdges node a
dissolve victims edges0 = foldr dissolve1 edges0 victims
    where
      dissolve1 :: (Eq a, Ord a) => a -> GraphEdges node a -> GraphEdges node a
      dissolve1 victim edges =
          -- Wherever the victim vertex appears as an out-edge, substitute the vOut set
          Map.mapWithKey (\k (h, s) -> (h, extend k s)) survivorEdges
          where
            -- Extend the out edges of one node through dissolved node v
            extend k s = if Set.member victim s then Set.union (Set.delete victim s) (Set.delete k vOut) else s
            -- Get the out-edges of the victim vertex (omitting self edges)
            vOut = Set.delete victim $ Set.unions $ List.map snd $ Map.elems victimEdges
            -- Split map into victim vertex and other vertices
            (victimEdges, survivorEdges) = partitionWithKey (\v _ -> (v == victim)) edges

-- | Monadic predicate version of 'dissolve'.
dissolveM :: (Functor m, Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges node a -> m (GraphEdges node a)
dissolveM victim edges = do
  victims <- Set.fromList <$> filterM victim (Map.keys edges)
  return $ dissolve victims edges

-- | Simplify a graph by throwing away the field information in each
-- node.  This means the nodes only contain the fully expanded Type
-- value (and any type synonyms.)
simpleEdges :: Monoid node => GraphEdges node TypeGraphVertex -> GraphEdges node TypeGraphVertex
simpleEdges = Map.mapWithKey (\v (n, s) -> (n, Set.delete v s)) .    -- delete any self edges
              Map.mapKeysWith combine simpleVertex .   -- simplify each vertex
              Map.map (over _2 (Set.map simpleVertex)) -- simplify the out edges
    where
      combine (n1, s1) (n2, s2) = (n1 <> n2, Set.union s1 s2)
