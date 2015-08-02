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
    , graphFromMap

    , allLensKeys
    , allPathKeys
    , allPathStarts
    , reachableFrom
    , reachableFromSimple
    , goalReachableFull
    , goalReachableSimple
    , goalReachableSimple'

    , makeTypeGraph
    , VertexStatus(..)
    , typeGraphEdges'
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
import Control.Monad (when)
import qualified Control.Monad.Reader as MTL (ask, ReaderT, runReaderT)
import Control.Monad.Reader.Extra (MonadReader(ask, local))
import Control.Monad.State.Extra (execStateT, MonadState(get), modify, StateT)
import Control.Monad.Trans (lift)
import Data.Default (Default(def))
import Data.Foldable as Foldable
import Data.Graph hiding (edges)
import Data.List as List (map)
import Data.Map as Map (alter, fromList, fromListWith, Map, update)
import qualified Data.Map as Map (toList)
import Data.Maybe (fromJust, mapMaybe)
import Data.Set.Extra as Set (empty, fromList, insert, map, member, Set, singleton, toList, union, unions)
import Data.Traversable as Traversable
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax (Quasi(..))
import Language.Haskell.TH.TypeGraph.Edges (GraphEdges, simpleEdges)
import Language.Haskell.TH.TypeGraph.Expand (E(E), ExpandMap, expandType)
import Language.Haskell.TH.TypeGraph.Prelude (adjacent', reachable')
import Language.Haskell.TH.TypeGraph.TypeInfo (startTypes, TypeInfo, typeVertex', fieldVertex)
import Language.Haskell.TH.TypeGraph.Stack (StackElement)
import Language.Haskell.TH.TypeGraph.Vertex (TGV, TGVSimple, vsimple, TypeGraphVertex, etype)
import Prelude hiding (any, concat, concatMap, elem, exp, foldr, mapM_, null, or)

instance Ppr Vertex where
    ppr n = ptext ("V" ++ show n)

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

data TypeGraph
    = TypeGraph
      { _typeInfo :: TypeInfo
      , _edges :: GraphEdges TGV
      , _graph :: (Graph, Vertex -> ((), TGV, [TGV]), TGV -> Maybe Vertex)
      , _gsimple :: (Graph, Vertex -> ((), TGVSimple, [TGVSimple]), TGVSimple -> Maybe Vertex)
      , _stack :: [StackElement]
      }

$(makeLenses ''TypeGraph)

instance (Monad m, MonadReader [StackElement] m) => MonadReader [StackElement] (MTL.ReaderT TypeGraph m) where
    ask = lift ask
    local f action = MTL.ask >>= MTL.runReaderT (local f (lift action))

allPathStarts :: forall m. (DsMonad m, MonadState (Map Type (E Type)) m, MonadReader TypeGraph m) => m (Set TGV)
allPathStarts = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- ask >>= return . view graph
  kernel <- ask >>= return . view typeInfo >>= \ti -> MTL.runReaderT (Traversable.mapM expandType (view startTypes ti) >>= Traversable.mapM typeVertex') ti
  let keep = Set.fromList $ concatMap (reachable g) (mapMaybe kf kernel)
      keep' = Set.map (view _2) . Set.map vf $ keep
  return keep'

view' :: MonadReader s m => Getting b s b -> m b
view' lns = view lns <$> ask

-- | Lenses represent steps in a path, but the start point is a type
-- vertex and the endpoint is a field vertex.
allLensKeys ::  (DsMonad m, MonadState (Map Type (E Type)) m, MonadReader TypeGraph m) => m (Map TGVSimple (Set TGV))
allLensKeys = do
  g <- view' graph
  gs <- view' gsimple
  allPathStarts >>= return . Map.fromListWith Set.union . List.map (\x -> (view vsimple x, Set.fromList (adjacent' g x))) . Set.toList

-- | Paths go between simple types.
allPathKeys :: (DsMonad m, MonadState (Map Type (E Type)) m, MonadReader TypeGraph m) => m (Map TGVSimple (Set TGVSimple))
allPathKeys = do
  gs <- view' gsimple
  allPathStarts >>= return . Map.fromList . List.map (\x -> (x, Set.fromList (reachable' gs x))) . Set.toList . Set.map (view vsimple)

reachableFrom :: forall m. (DsMonad m, MonadReader TypeGraph m) => TGV -> m (Set TGV)
reachableFrom v = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- view' graph
  case kf v of
    Nothing -> return Set.empty
    Just v' -> return $ Set.map (\(_, key, _) -> key) . Set.map vf $ Set.fromList $ reachable (transposeG g) v'

reachableFromSimple :: forall m. (DsMonad m, MonadReader TypeGraph m) => TGVSimple -> m (Set TGVSimple)
reachableFromSimple v = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- view' gsimple
  case kf v of
    Nothing -> return Set.empty
    Just v' -> return $ Set.map (\(_, key, _) -> key) . Set.map vf $ Set.fromList $ reachable (transposeG g) v'

-- | Can we reach the goal type from the start type in this key?
goalReachableFull :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TGV -> TGV -> m Bool
goalReachableFull gkey key0 = isReachable gkey key0 <$> view' graph

goalReachableSimple :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TGVSimple -> TGVSimple -> m Bool
goalReachableSimple gkey key0 = isReachable gkey key0 <$> view' gsimple

goalReachableSimple' :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TGV -> TGV -> m Bool
goalReachableSimple' gkey key0 = isReachable (view vsimple gkey) (view vsimple key0) <$> view' gsimple

isReachable :: TypeGraphVertex key => key -> key -> (Graph, Vertex -> ((), key, [key]), key -> Maybe Vertex) -> Bool
isReachable gkey key0 (g, _vf, kf) = path g (fromJust $ kf key0) (fromJust $ kf gkey)

-- | Return the TGV associated with a particular type,
-- with no field specified.
typeGraphVertex :: (MonadReader TypeGraph m, MonadState ExpandMap m, DsMonad m) => Type -> m TGV
typeGraphVertex typ = do
        typ' <- expandType typ
        ask >>= MTL.runReaderT (typeVertex' typ') . view typeInfo
        -- magnify typeInfo $ vertex Nothing typ'

-- | Return the TGV associated with a particular type and field.
typeGraphVertexOfField :: (MonadReader TypeGraph m, MonadState (Map Type (E Type)) m, DsMonad m) => (Name, Name, Either Int Name) -> Type -> m TGV
typeGraphVertexOfField fld typ = do
        typ' <- expandType typ
        ask >>= MTL.runReaderT (fieldVertex fld typ') . view typeInfo
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

--- type Edges = GraphEdges TGV

-- | Return the set of edges implied by the subtype relationship among
-- a set of types.  This is just the nodes of the type graph.  The
-- type aliases are expanded by the th-desugar package to make them
-- suitable for use as map keys.
typeGraphEdges'
    :: forall m. (DsMonad m, MonadReader TypeGraph m, MonadState (Set TGV) m, MonadState (Map Type (E Type)) m) =>
       (TGV -> m (Set TGV))
           -- ^ This function is applied to every expanded type before
           -- use, and the result is used instead.  If it returns
           -- NoVertex, no vertices or edges are added to the graph.
           -- If it returns Sink no outgoing edges are added.  The
           -- current use case Substitute is to see if there is an
           -- instance of class @View a b@ where @a@ is the type
           -- passed to @doType@, and replace it with @b@, and use the
           -- lens returned by @View's@ method to convert between @a@
           -- and @b@ (i.e. to implement the edge in the type graph.)
    -> [Type]
    -> m (GraphEdges TGV)
typeGraphEdges' augment types = do
  execStateT (mapM_ (\typ -> lift (typeGraphVertex typ) >>= doNode) types) (mempty :: GraphEdges TGV)
    where
      doNode v = do
        (s :: Set TGV) <- lift get
        when (not (member v s)) $
             do lift $ modify (Set.insert v)
                doNode' v
      doNode' :: TGV -> StateT (GraphEdges TGV) m ()
      doNode' typ = do
        addNode typ
        vs <- lift $ augment typ
        mapM_ (addEdge typ) (Set.toList vs)
        mapM_ doNode (Set.toList vs)

      addNode :: TGV -> StateT (GraphEdges TGV) m ()
      addNode a = modify (Map.alter (maybe (Just Set.empty) Just) a :: Map TGV (Set TGV) -> Map TGV (Set TGV))

      addEdge :: TGV -> TGV -> StateT (GraphEdges TGV) m ()
      addEdge a b = modify $ Map.update (\s -> Just (Set.insert b s)) a

-- | Return the set of adjacent vertices according to the default type
-- graph - i.e. the one determined only by the type definitions, not
-- by any additional hinting function.
adjacent :: forall m. (MonadReader TypeGraph m, DsMonad m, MonadState (Map Type (E Type)) m) => TGV -> m (Set TGV)
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

-- FIXME: pass in ti, pass in makeTypeGraphEdges, remove Q, move to TypeGraph.Graph
makeTypeGraph :: MonadReader TypeInfo m => (GraphEdges TGV) -> m TypeGraph
makeTypeGraph es = do
  ti <- ask
  return $ TypeGraph
             { _typeInfo = ti
             , _edges = es
             , _graph = graphFromMap es
             , _gsimple = graphFromMap (simpleEdges es)
             , _stack = []
             }
