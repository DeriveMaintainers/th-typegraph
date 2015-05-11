-- | Abstract operations on Maps containing graph edges.

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Haskell.TH.TypeGraph.Graph
    ( GraphEdges
    , cutVertex
    , cutVertices
    , cutVerticesM
    , mergeVertex
    , mergeVertices
    , mergeVerticesM
    , partitionM
    , flatten
    , graphFromMap
    ) where

import Control.Lens (over, _2)
import Control.Monad (filterM)
import Data.Graph hiding (edges)
import Data.List as List
import Data.Map as Map
import Data.Set as Set
import Language.Haskell.TH (Ppr(ppr))
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.TypeGraph.Core (pprint')

type GraphEdges label key = Map key (label, Set key)

instance Ppr key => Ppr (GraphEdges label key) where
    ppr x =
        ptext $ intercalate "\n  " $
          "edges:" : (List.map
                       (\ (k, (_, ks)) -> intercalate "\n    " ((pprint' k ++ "->") : List.map pprint' (Set.toList ks)))
                       (Map.toList x))

-- | Remove a node and all its in- and out-edges.
cutVertex :: (Eq a, Ord a) => a -> GraphEdges label a -> GraphEdges label a
cutVertex victim edges = Map.map (over _2 (Set.filter (/= victim))) $ Map.filterWithKey (\k _ -> k /= victim) edges

-- | Cut vertices for which the predicate returns False
cutVertices :: (Eq a, Ord a) => (a -> Bool) -> GraphEdges label a -> GraphEdges label a
cutVertices victim edges = List.foldr cutVertex edges (List.filter victim (Map.keys edges))

-- | Cut vertices for which the predicate returns False
cutVerticesM :: (Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges label a -> m (GraphEdges label a)
cutVerticesM victim edges = do
  victims <- filterM victim (Map.keys edges) >>= return . Set.fromList
  return $ cutVertices (`Set.member` victims) edges

-- | Merge a node into the nodes that are its in-edges.
mergeVertex :: (Eq a, Ord a) => a -> GraphEdges label a -> GraphEdges label a
mergeVertex victim edges =
  survivorEdges'
    where
      -- Wherever the victim vertex appears as an out-edge, substitute the victimOut set
      survivorEdges' = Map.mapWithKey (\ k (node, s) -> (node, if Set.member victim s then Set.union (Set.delete victim s) (Set.delete k victimOut) else s)) survivorEdges
      -- Split map into victim vertex and other vertices
      (victimEdges, survivorEdges) = partitionWithKey (\ v _ -> (v == victim)) edges
      -- Get the out-edges of the victim vertex
      victimOut = Set.delete victim $ Set.unions $ List.map snd $ Map.elems victimEdges

mergeVertices :: (Eq a, Ord a) => (a -> Bool) -> GraphEdges label a -> GraphEdges label a
mergeVertices keep edges = List.foldr mergeVertex edges (List.filter (not . keep) (Map.keys edges))

mergeVerticesM :: (Monad m, Ord  a) => (a -> m Bool) -> GraphEdges label a -> m (GraphEdges label a)
mergeVerticesM predicateM edges =
    mapM predicateM (Map.keys edges) >>= \flags -> return $ mergeVertices (makePredicate (zip (Map.keys edges) flags)) edges
    where
      makePredicate :: Ord a => [(a, Bool)] -> a -> Bool
      makePredicate pairs = flip (Map.findWithDefault False) (Map.fromList pairs)

partitionM :: forall m a. Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM p l = do
  (flags :: [Bool]) <- mapM p l
  let pairs :: [(a, Bool)]
      pairs = zip l flags
      as :: [(a, Bool)]
      bs :: [(a, Bool)]
      (as, bs) = List.partition snd pairs
  return $ (List.map fst as, List.map fst bs)

flatten :: Ord a => Set (Set a) -> Set a
flatten = Set.fold Set.union Set.empty


-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
graphFromMap :: forall label key. (Ord key) =>
                GraphEdges label key -> (Graph, Vertex -> (label, key, [key]), key -> Maybe Vertex)
graphFromMap mp =
    graphFromEdges triples
    where
      triples :: [(label, key, [key])]
      triples = List.map (\ (k, (node, ks)) -> (node, k, Set.toList ks)) $ Map.toList mp
