-- | Abstract operations on Maps containing graph edges.

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Haskell.TH.TypeGraph.TypeGraph
    ( TypeGraph, typeInfo, edges, graph, gsimple, stack
    , makeTypeGraph
    , graphFromMap

    -- * TypeGraph queries
    , allLensKeys
    , allPathKeys
    , allPathStarts
    , reachableFrom
    , reachableFromSimple
    , goalReachableFull
    , goalReachableSimple
    , goalReachableSimple'

    , VertexStatus(..)
    , adjacent
    , typeGraphVertex
    , typeGraphVertexOfField
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
import Data.Monoid (mempty)
#else
import Control.Applicative
#endif
import Control.Lens
-- import Control.Monad (when)
import qualified Control.Monad.Reader as MTL (ask, ReaderT, runReaderT)
import Control.Monad.Readers (MonadReaders(askPoly, localPoly))
import Control.Monad.States (MonadStates)
import Control.Monad.Trans (lift)
import Data.Default (Default(def))
import Data.Foldable as Foldable
import Data.Graph hiding (edges)
import Data.List as List (map)
import Data.Map as Map (fromList, fromListWith, Map)
import qualified Data.Map as Map (toList)
import Data.Maybe (fromJust, mapMaybe)
import Data.Set.Extra as Set (empty, fromList, map, Set, singleton, toList, union, unions)
import Data.Traversable as Traversable
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (ptext, vcat)
import Language.Haskell.TH.Syntax (Quasi(..))
import Language.Haskell.TH.TypeGraph.Edges (GraphEdges, simpleEdges)
import Language.Haskell.TH.TypeGraph.Expand (E(E), ExpandMap, expandType)
import Language.Haskell.TH.TypeGraph.Prelude (adjacent', reachable')
import Language.Haskell.TH.TypeGraph.TypeInfo (startTypes, TypeInfo, typeVertex', fieldVertex)
import Language.Haskell.TH.TypeGraph.Stack (StackElement)
import Language.Haskell.TH.TypeGraph.Vertex (TGV, TGVSimple, vsimple, TypeGraphVertex, etype)
import Prelude hiding (any, concat, concatMap, elem, exp, foldr, mapM_, null, or)

data TypeGraph
    = TypeGraph
      { _typeInfo :: TypeInfo
      , _edges :: GraphEdges TGV
      , _graph :: (Graph, Vertex -> ((), TGV, [TGV]), TGV -> Maybe Vertex)
      , _gsimple :: (Graph, Vertex -> ((), TGVSimple, [TGVSimple]), TGVSimple -> Maybe Vertex)
      , _stack :: [StackElement]
      }

-- | Build a TypeGraph given a set of edges and the TypeInfo environment
makeTypeGraph :: MonadReaders TypeInfo m => (GraphEdges TGV) -> m TypeGraph
makeTypeGraph es = do
  ti <- askPoly
  return $ TypeGraph
             { _typeInfo = ti
             , _edges = es
             , _graph = graphFromMap es
             , _gsimple = graphFromMap (simpleEdges es)
             , _stack = []
             }

-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
graphFromMap :: forall key. (Ord key) =>
                GraphEdges key -> (Graph, Vertex -> ((), key, [key]), key -> Maybe Vertex)
graphFromMap mp =
    graphFromEdges triples
    where
      triples :: [((), key, [key])]
      triples = List.map (\ (k, ks) -> ((), k, Foldable.toList ks)) $ Map.toList mp

$(makeLenses ''TypeGraph)

instance (Monad m, MonadReaders [StackElement] m) => MonadReaders [StackElement] (MTL.ReaderT TypeGraph m) where
    askPoly = lift askPoly
    localPoly f action = MTL.ask >>= MTL.runReaderT (localPoly f (lift action))

instance Ppr Vertex where
    ppr n = ptext ("V" ++ show n)

instance Ppr (Graph, Vertex -> ((), TGV, [TGV]), TGV -> Maybe Vertex) where
    ppr (g, vf, _) = vcat (List.map (ppr . vf) (vertices g))

instance Ppr (Graph, Vertex -> ((), TGVSimple, [TGVSimple]), TGVSimple -> Maybe Vertex) where
    ppr (g, vf, _) = vcat (List.map (ppr . vf) (vertices g))

allPathStarts :: forall m. (DsMonad m, MonadStates ExpandMap m, MonadReaders TypeGraph m) => m (Set TGV)
allPathStarts = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- askPoly >>= return . view graph
  kernel <- askPoly >>= return . view typeInfo >>= \ti -> MTL.runReaderT (Traversable.mapM expandType (view startTypes ti) >>= Traversable.mapM typeVertex') ti
  let keep = Set.fromList $ concatMap (reachable g) (mapMaybe kf kernel)
      keep' = Set.map (view _2) . Set.map vf $ keep
  return keep'

view' :: MonadReaders s m => Getting b s b -> m b
view' lns = view lns <$> askPoly

-- | Lenses represent steps in a path, but the start point is a type
-- vertex and the endpoint is a field vertex.
allLensKeys ::  (DsMonad m, MonadStates ExpandMap m, MonadReaders TypeGraph m) => m (Map TGVSimple (Set TGV))
allLensKeys = do
  g <- view' graph
  -- gs <- view' gsimple
  allPathStarts >>= return . Map.fromListWith Set.union . List.map (\x -> (view vsimple x, Set.fromList (adjacent' g x))) . Set.toList

-- | Paths go between simple types.
allPathKeys :: (DsMonad m, MonadStates ExpandMap m, MonadReaders TypeGraph m) => m (Map TGVSimple (Set TGVSimple))
allPathKeys = do
  gs <- view' gsimple
  allPathStarts >>= return . Map.fromList . List.map (\x -> (x, Set.fromList (reachable' gs x))) . Set.toList . Set.map (view vsimple)

reachableFrom :: forall m. (DsMonad m, MonadReaders TypeGraph m) => TGV -> m (Set TGV)
reachableFrom v = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- view' graph
  case kf v of
    Nothing -> return Set.empty
    Just v' -> return $ Set.map (\(_, key, _) -> key) . Set.map vf $ Set.fromList $ reachable (transposeG g) v'

reachableFromSimple :: forall m. (DsMonad m, MonadReaders TypeGraph m) => TGVSimple -> m (Set TGVSimple)
reachableFromSimple v = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- view' gsimple
  case kf v of
    Nothing -> return Set.empty
    Just v' -> return $ Set.map (\(_, key, _) -> key) . Set.map vf $ Set.fromList $ reachable (transposeG g) v'

-- | Can we reach the goal type from the start type in this key?
goalReachableFull :: (Functor m, DsMonad m, MonadReaders TypeGraph m) => TGV -> TGV -> m Bool
goalReachableFull gkey key0 = isReachable gkey key0 <$> view' graph

-- | Can we reach the goal type in the simplified graph?
goalReachableSimple :: (Functor m, DsMonad m, MonadReaders TypeGraph m) => TGVSimple -> TGVSimple -> m Bool
goalReachableSimple gkey key0 = isReachable gkey key0 <$> view' gsimple

-- | Version of goalReachableSimple that first simplifies its argument nodes
goalReachableSimple' :: (Functor m, DsMonad m, MonadReaders TypeGraph m) => TGV -> TGV -> m Bool
goalReachableSimple' gkey key0 = goalReachableSimple (view vsimple gkey) (view vsimple key0)

isReachable :: TypeGraphVertex key => key -> key -> (Graph, Vertex -> ((), key, [key]), key -> Maybe Vertex) -> Bool
isReachable gkey key0 (g, _vf, kf) = path g (fromJust $ kf key0) (fromJust $ kf gkey)

-- | Return the TGV associated with a particular type,
-- with no field specified.
typeGraphVertex :: (MonadReaders TypeGraph m, MonadStates ExpandMap m, DsMonad m) => Type -> m TGV
typeGraphVertex typ = do
        typ' <- expandType typ
        askPoly >>= MTL.runReaderT (typeVertex' typ') . view typeInfo
        -- magnify typeInfo $ vertex Nothing typ'

-- | Return the TGV associated with a particular type and field.
typeGraphVertexOfField :: (MonadReaders TypeGraph m, MonadStates ExpandMap m, DsMonad m) =>
                          (Name, Name, Either Int Name) -> Type -> m TGV
typeGraphVertexOfField fld typ = do
        typ' <- expandType typ
        askPoly >>= MTL.runReaderT (fieldVertex fld typ') . view typeInfo
        -- magnify typeInfo $ vertex (Just fld) typ'

-- type TypeGraphEdges typ = Map typ (Set typ)

-- | When a VertexStatus value is associated with a Type it describes
-- alterations in the type graph from the usual default.
data VertexStatus typ
    = Vertex      -- ^ normal case
    | Sink        -- ^ out degree zero - don't create any outgoing edges
    | Divert typ  -- ^ replace all outgoing edges with an edge to an alternate type
    | Extra typ   -- ^ add an extra outgoing edge to the given type
    deriving Show

instance Default (VertexStatus typ) where
    def = Vertex

-- | Return the set of adjacent vertices according to the default type
-- graph - i.e. the one determined only by the type definitions, not
-- by any additional hinting function.
adjacent :: forall m. (MonadReaders TypeGraph m, DsMonad m, MonadStates ExpandMap m) => TGV -> m (Set TGV)
adjacent typ =
    case view (vsimple . etype) typ of
      E (ForallT _ _ typ') -> typeGraphVertex typ' >>= adjacent
      E (AppT c e) ->
          typeGraphVertex c >>= \c' ->
          typeGraphVertex e >>= \e' ->
          return $ Set.fromList [c', e']
      E (ConT name) -> do
        info <- qReify name
        case info of
          TyConI dec -> doDec dec
          _ -> return mempty
      _typ -> return $ {-trace ("Unrecognized type: " ++ pprint' typ)-} mempty
    where
      doDec :: Dec -> m (Set TGV)
      doDec dec@(NewtypeD _ tname _ con _) = doCon tname dec con
      doDec dec@(DataD _ tname _ cns _) = Set.unions <$> Traversable.mapM (doCon tname dec) cns
      doDec (TySynD _tname _tvars typ') = singleton <$> typeGraphVertex typ'
      doDec _ = return mempty

      doCon :: Name -> Dec -> Con -> m (Set TGV)
      doCon tname dec (ForallC _ _ con) = doCon tname dec con
      doCon tname dec (NormalC cname fields) = Set.unions <$> Traversable.mapM (doField tname dec cname) (zip (List.map Left ([1..] :: [Int])) (List.map snd fields))
      doCon tname dec (RecC cname fields) = Set.unions <$> Traversable.mapM (doField tname dec cname) (List.map (\ (fname, _, typ') -> (Right fname, typ')) fields)
      doCon tname dec (InfixC (_, lhs) cname (_, rhs)) = Set.unions <$> Traversable.mapM (doField tname dec cname) [(Left 1, lhs), (Left 2, rhs)]

      doField :: Name -> Dec -> Name -> (Either Int Name, Type) -> m (Set TGV)
      doField tname _dec cname (fld, ftype) = Set.singleton <$> typeGraphVertexOfField (tname, cname, fld) ftype
