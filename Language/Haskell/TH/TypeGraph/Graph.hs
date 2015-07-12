-- | Abstract operations on Maps containing graph edges.

-- FIXME: the sense of the predicates are kinda mixed up here

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Haskell.TH.TypeGraph.Graph
    ( TypeGraph, typeInfo, edges, graph, gsimple
    , TypeGraph(TypeGraph, _typeInfo, _edges, _graph, _gsimple, _stack) -- temporary
    , graphFromMap

    , allLensKeys
    , allPathKeys
    , reachableFrom
    , goalReachableFull
    , goalReachableSimple
    ) where

import Control.Lens (makeLenses, view, (%~))
import Control.Monad (filterM)
import Control.Monad.Reader (ask, local, MonadReader, ReaderT, runReaderT)
import Data.Foldable as Foldable
import Data.Graph hiding (edges)
import Data.List as List (intercalate, map)
import Data.Map as Map (keys)
import qualified Data.Map as Map (toList)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set as Set (empty, fromList, map, Set)
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.TypeGraph.Edges (GraphEdges)
import Language.Haskell.TH.TypeGraph.Expand (expandType)
import Language.Haskell.TH.TypeGraph.Info (startTypes, TypeInfo, vertex)
import Language.Haskell.TH.TypeGraph.Shape (pprint')
import Language.Haskell.TH.TypeGraph.Stack (HasStack(withStack, push), StackElement(StackElement))
import Language.Haskell.TH.TypeGraph.Vertex (simpleVertex, TypeGraphVertex)
import Prelude hiding (any, concat, concatMap, elem, exp, foldr, mapM_, null, or)

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

data TypeGraph
    = TypeGraph
      { _typeInfo :: TypeInfo
      , _edges :: GraphEdges () TypeGraphVertex
      , _graph :: (Graph, Vertex -> ((), TypeGraphVertex, [TypeGraphVertex]), TypeGraphVertex -> Maybe Vertex)
      , _gsimple :: (Graph, Vertex -> ((), TypeGraphVertex, [TypeGraphVertex]), TypeGraphVertex -> Maybe Vertex)
      , _stack :: [StackElement] -- this is the only type that isn't available in th-typegraph
      }

$(makeLenses ''TypeGraph)

instance Monad m => HasStack (ReaderT TypeGraph m) where
    withStack f = ask >>= f . view stack
    push fld con dec action = local (stack %~ (\s -> StackElement fld con dec : s)) action

-- | A lens key is a pair of vertexes corresponding to a Path instance.
allLensKeys :: (DsMonad m, MonadReader TypeGraph m) => m (Set (TypeGraphVertex, TypeGraphVertex))
allLensKeys = do
  pathKeys <- allPathKeys
  Set.fromList <$> filterM (uncurry goalReachableSimple) [ (g, k) | g <- toList (Set.map simpleVertex pathKeys), k <- toList (Set.map simpleVertex pathKeys) ]

allPathKeys :: forall m. (DsMonad m, MonadReader TypeGraph m) => m (Set TypeGraphVertex)
allPathKeys = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- view graph
  kernel <- view typeInfo >>= \ti -> runReaderT (mapM expandType (view startTypes ti) >>= mapM (vertex Nothing)) ti
  let kernel' = mapMaybe kf kernel
  let keep = Set.fromList $ concatMap (reachable g) kernel'
      keep' = Set.map (\(_, key, _) -> key) . Set.map vf $ keep
  return keep'

reachableFrom :: forall m. (DsMonad m, MonadReader TypeGraph m) => TypeGraphVertex -> m (Set TypeGraphVertex)
reachableFrom v = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- view graph
  case kf v of
    Nothing -> return Set.empty
    Just v' -> return $ Set.map (\(_, key, _) -> key) . Set.map vf $ Set.fromList $ reachable (transposeG g) v'

isReachable :: (Functor m, DsMonad m, MonadReader TypeGraph m) =>
               TypeGraphVertex -> TypeGraphVertex -> (Graph, Vertex -> ((), TypeGraphVertex, [TypeGraphVertex]), TypeGraphVertex -> Maybe Vertex) -> m Bool
isReachable gkey key0 (g, _vf, kf) = do
  es <- view edges
  case kf key0 of
    Nothing -> error ("isReachable - unknown key: " ++ pprint' key0)
    Just key -> do
      let gvert = fromMaybe (error $ "Unknown goal type: " ++ pprint' gkey ++ "\n" ++ intercalate "\n  " ("known:" : List.map pprint' (Map.keys es))) (kf gkey)
      -- Can we reach any node whose type matches (ConT gname)?  Fields don't matter.
      return $ elem gvert (reachable g key)

-- | Can we reach the goal type from the start type in this key?
goalReachableFull :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TypeGraphVertex -> TypeGraphVertex -> m Bool
goalReachableFull gkey key0 = view graph >>= isReachable gkey key0

goalReachableSimple :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TypeGraphVertex -> TypeGraphVertex -> m Bool
goalReachableSimple gkey key0 = view gsimple >>= isReachable (simpleVertex gkey) (simpleVertex key0)
