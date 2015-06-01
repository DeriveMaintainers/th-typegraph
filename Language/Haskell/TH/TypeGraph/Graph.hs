-- | Abstract operations on Maps containing graph edges.

-- FIXME: the sense of the predicates are kinda mixed up here

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Haskell.TH.TypeGraph.Graph
    ( GraphEdges
    , graphFromMap
    , cut
    , cutM
    , isolate
    , isolateM
    , dissolve
    , dissolveM
    ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>))
#endif

import Control.Lens (over, _2)
import Control.Monad (filterM)
import Data.Foldable as Foldable
import Data.Graph hiding (edges)
import Data.List as List (intercalate, map)
import Data.Map as Map (Map, elems, filterWithKey, keys, map, mapWithKey, partitionWithKey)
import qualified Data.Map as Map (toList)
import Data.Set as Set (Set, delete, empty, filter, member, fromList, union, unions)
import Language.Haskell.TH (Ppr(ppr))
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.TypeGraph.Core (pprint')
import Prelude hiding (foldr)

type GraphEdges node key = Map key (node, Set key)

instance Ppr key => Ppr (GraphEdges node key) where
    ppr x =
        ptext $ intercalate "\n  " $
          "edges:" : (List.map
                       (\(k, (_, ks)) -> intercalate "\n    " ((pprint' k ++ " ->") : List.map pprint' (toList ks)))
                       (Map.toList x))

-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
graphFromMap :: forall node key. (Ord key) =>
                GraphEdges node key -> (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
graphFromMap mp =
    graphFromEdges triples
    where
      triples :: [(node, key, [key])]
      triples = List.map (\ (k, (node, ks)) -> (node, k, toList ks)) $ Map.toList mp

-- | Isolate and remove some nodes
cut :: (Eq a, Ord a) => Set a -> GraphEdges node a -> GraphEdges node a
cut victims edges = Map.filterWithKey (\v _ -> not (Set.member v victims)) (isolate victims edges)

-- | Monadic predicate version of 'cut'.
cutM :: (Functor m, Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges node a -> m (GraphEdges node a)
cutM victim edges = do
  victims <- Set.fromList <$> filterM victim (Map.keys edges)
  return $ cut victims edges

-- | Remove all the in- and out-edges of some nodes
isolate :: (Eq a, Ord a) => Set a -> GraphEdges node a -> GraphEdges node a
isolate victims edges =
    edges''
    where
      edges' = Map.mapWithKey (\v (h, s) -> (h, if Set.member v victims then Set.empty else s)) edges -- Remove the out-edges
      edges'' = Map.map (over _2 (Set.filter (not . (`Set.member` victims)))) edges' -- Remove the in-edges

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
