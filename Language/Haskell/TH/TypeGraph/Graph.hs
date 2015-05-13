-- | Abstract operations on Maps containing graph edges.

-- FIXME: the sense of the predicates are kinda mixed up here

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Haskell.TH.TypeGraph.Graph
    ( GraphEdges
    , graphFromMap

    , cutVertex
    , cutVertices
    , cutVerticesM
    , isolateVertex
    , isolateVertices
    , isolateVerticesM
    , mergeVertex
    , mergeVertices
    , mergeVerticesM

    , cut
    , cutM
    , isolate
    , isolateM
    , dissolve
    , dissolveM

    , partitionM
    , flatten
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

import Debug.Trace

type GraphEdges label key = Map key (label, Set key)

instance Ppr key => Ppr (GraphEdges label key) where
    ppr x =
        ptext $ intercalate "\n  " $
          "edges:" : (List.map
                       (\ (k, (_, ks)) -> intercalate "\n    " ((pprint' k ++ "->") : List.map pprint' (Set.toList ks)))
                       (Map.toList x))

-- | Remove a node and all its in- and out-edges.
cutVertex :: (Eq a, Ord a, Eq label) => a -> GraphEdges label a -> GraphEdges label a
cutVertex victim edges =
    let old = Map.map (over _2 (Set.filter (/= victim))) $ Map.filterWithKey (\k _ -> k /= victim) edges
        new = cut (/= victim) edges in
    if old /= new then error "cutVertex" else new

-- | Cut vertices for which the predicate returns False
cutVertices :: (Eq a, Ord a, Eq label) => (a -> Bool) -> GraphEdges label a -> GraphEdges label a
cutVertices victim edges =
    let old = List.foldr cutVertex edges (List.filter victim (Map.keys edges))
        new = cut (not . victim) edges in
    if old /= new then error "cutVertices" else new

-- | Cut vertices for which the predicate returns False
cutVerticesM :: (Monad m, Eq a, Ord a, Eq label) => (a -> m Bool) -> GraphEdges label a -> m (GraphEdges label a)
cutVerticesM victim edges = do
  victims <- filterM victim (Map.keys edges) >>= return . Set.fromList
  let old = cutVertices (`Set.member` victims) edges
  new <- cutM (\x -> victim x >>= return . not) edges
  if old /= new then error "cutVerticesM" else return new

-- | Remove all of a node's in- and out-edges.
isolateVertex :: (Eq a, Ord a, Ppr a, Eq label) => a -> GraphEdges label a -> GraphEdges label a
isolateVertex victim edges =
    let old = Map.map (over _2 (Set.filter (/= victim))) $ Map.alter (fmap (\ (h, _) -> (h, Set.empty))) (trace ("isolateVertex: " ++ pprint' victim) victim) edges
        new = isolate (/= victim) edges in
    if old /= new then error "isolateVertex" else new

-- | Cut vertices for which the predicate returns False
isolateVertices :: (Eq a, Ord a, Ppr a, Eq label) => (a -> Bool) -> GraphEdges label a -> GraphEdges label a
isolateVertices victim edges =
    let old = List.foldr isolateVertex edges (List.filter victim (Map.keys edges))
        new = isolate (not . victim) edges in
    if old /= new then error "isolateVertices" else new

-- | Cut vertices for which the predicate returns False
isolateVerticesM :: (Monad m, Eq a, Ord a, Ppr a, Eq label) => (a -> m Bool) -> GraphEdges label a -> m (GraphEdges label a)
isolateVerticesM victim edges = do
  victims <- filterM victim (Map.keys edges) >>= return . Set.fromList
  let old = isolateVertices (`Set.member` victims) edges
  new <- isolateM (\x -> victim x >>= return . not) edges
  if old /= new then error "isolateVerticesM" else return new

-- | Merge a node into the nodes that are its in-edges.
mergeVertex :: (Eq a, Ord a, Eq label) => a -> GraphEdges label a -> GraphEdges label a
mergeVertex victim edges =
    let old = survivorEdges'
        new = dissolve (/= victim) edges in
    if old /= new then error "mergeVertex" else new
    where
      -- Wherever the victim vertex appears as an out-edge, substitute the victimOut set
      survivorEdges' = Map.mapWithKey (\ k (node, s) -> (node, if Set.member victim s then Set.union (Set.delete victim s) (Set.delete k victimOut) else s)) survivorEdges
      -- Split map into victim vertex and other vertices
      (victimEdges, survivorEdges) = partitionWithKey (\ v _ -> (v == victim)) edges
      -- Get the out-edges of the victim vertex
      victimOut = Set.delete victim $ Set.unions $ List.map snd $ Map.elems victimEdges

mergeVertices :: (Eq a, Ord a, Eq label) => (a -> Bool) -> GraphEdges label a -> GraphEdges label a
mergeVertices keep edges =
    let old = List.foldr mergeVertex edges (List.filter (not . keep) (Map.keys edges))
        new = dissolve keep edges in
    if old /= new then error "mergeVertices" else new

mergeVerticesM :: (Monad m, Ord  a, Eq label) => (a -> m Bool) -> GraphEdges label a -> m (GraphEdges label a)
mergeVerticesM predicateM edges = do
  old <- mapM predicateM (Map.keys edges) >>= \flags -> return $ mergeVertices (makePredicate (zip (Map.keys edges) flags)) edges
  new <- dissolveM predicateM edges
  if old /= new then error "mergeVerticesM" else return new
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

-- | Isolate and remove some nodes
cut :: (Eq a, Ord a) => (a -> Bool) -> GraphEdges label a -> GraphEdges label a
cut p edges = Map.filterWithKey (\v _ -> p v) (isolate p edges)

cutM :: (Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges label a -> m (GraphEdges label a)
cutM p edges = do
  p' <- filterM p (Map.keys edges) >>= return . flip Set.member . Set.fromList
  return $ cut p' edges

-- | Remove all the in- and out-edges of some nodes
isolate :: (Eq a, Ord a) => (a -> Bool) -> GraphEdges label a -> GraphEdges label a
isolate p edges =
    edges''
    where
      edges' = Map.mapWithKey (\v (h, s) -> (h, if p v then s else Set.empty)) edges -- Remove the out-edges
      edges'' = Map.map (over _2 (Set.filter p)) edges'                               -- Remove the in-edges

isolateM :: (Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges label a -> m (GraphEdges label a)
isolateM p edges = do
  p' <- filterM p (Map.keys edges) >>= return . flip Set.member . Set.fromList
  return $ isolate p' edges

-- | Remove some nodes and extend each of their in-edges to each of
-- their out-edges
dissolve :: (Eq a, Ord a) => (a -> Bool) -> GraphEdges label a -> GraphEdges label a
dissolve p edges = List.foldr dissolve1 edges (List.filter (not . p) (Map.keys edges))

dissolveM :: (Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges label a -> m (GraphEdges label a)
dissolveM p edges = do
  p' <- filterM p (Map.keys edges) >>= return . flip Set.member . Set.fromList
  return $ dissolve p' edges

dissolve1 :: (Eq a, Ord a) => a -> GraphEdges label a -> GraphEdges label a
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
