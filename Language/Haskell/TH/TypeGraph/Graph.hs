-- | Abstract operations on Maps containing graph edges.

-- FIXME: the sense of the predicates are kinda mixed up here

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Haskell.TH.TypeGraph.Graph
    ( TypeGraph, typeInfo, edges, graph, gsimple
    , TypeGraph(TypeGraph, _typeInfo, _edges, _graph, _gsimple, _stack) -- temporary
    , graphFromMap

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
import Control.Lens -- (makeLenses, over, view)
import Control.Monad (when)
import Control.Monad as List (filterM)
import Control.Monad.Reader (ask, local, MonadReader, ReaderT, runReaderT)
import Control.Monad.State (execStateT, modify, StateT)
import Control.Monad.Trans (lift)
import Data.Default (Default(def))
import Data.Foldable as Foldable
import Data.Graph hiding (edges)
import Data.List as List (map)
import Data.Map as Map (alter, update)
import qualified Data.Map as Map (toList)
import Data.Maybe (fromJust, mapMaybe)
import Data.Set.Extra as Set (empty, flatten, filterM, fromList, insert, map, mapM, member, Set, singleton, toList, unions)
import Data.Traversable as Traversable
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax (Quasi(..))
import Language.Haskell.TH.TypeGraph.Edges (GraphEdges, simpleEdges)
import Language.Haskell.TH.TypeGraph.Expand (E(E), expandType)
import Language.Haskell.TH.TypeGraph.Info (startTypes, TypeInfo, typeVertex', fieldVertex)
import Language.Haskell.TH.TypeGraph.Prelude (HasSet(getSet, modifySet))
import Language.Haskell.TH.TypeGraph.Stack (HasStack(withStack, push), StackElement(StackElement))
import Language.Haskell.TH.TypeGraph.Vertex (simpleVertex, TGV, TGVSimple, vsimple, TypeGraphVertex, etype)
import Prelude hiding (any, concat, concatMap, elem, exp, foldr, mapM_, null, or)

instance Ppr Vertex where
    ppr n = ptext ("V" ++ show n)

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
      triples = List.map (\ (k, (node, ks)) -> (node, k, Foldable.toList ks)) $ Map.toList mp

data TypeGraph
    = TypeGraph
      { _typeInfo :: TypeInfo
      , _edges :: GraphEdges () TGV
      , _graph :: (Graph, Vertex -> ((), TGV, [TGV]), TGV -> Maybe Vertex)
      , _gsimple :: (Graph, Vertex -> ((), TGVSimple, [TGVSimple]), TGVSimple -> Maybe Vertex)
      , _stack :: [StackElement] -- this is the only type that isn't available in th-typegraph
      }

$(makeLenses ''TypeGraph)

instance Monad m => HasStack (ReaderT TypeGraph m) where
    withStack f = ask >>= f . view stack
    push fld con dec action = local (stack %~ (\s -> StackElement fld con dec : s)) action

#if 0
-- | All the types for which we will generate Path types, along with
-- the corresponding set of goal types.
allKeys :: (DsMonad m, MonadReader TypeGraph m) => m (Set (TGV, Set TGV, Set TGV))
allKeys = do
  (g, vf, kf) <- view graph
  -- (gs, vfs, kfs) <- view gsimple
  ti <- view typeInfo
  st <- runReaderT (Traversable.mapM expandType (view startTypes ti) >>= Traversable.mapM (vertex Nothing)) ti
  let st' = mapMaybe kf st
  let pt = Set.fromList $ concatMap (reachable g) st'
      pt' = Set.map (\(_, key, _) -> key) . Set.map vf $ pt
      pt'' = Set.map simpleVertex pt'
  Set.mapM (\t -> do goals <- Set.filterM (\g -> goalReachableSimple g t) pt''
                     let Just v = vf t
                         (_, _, adjacent) <- kf v
                     return (t, Set.fromList adjacent, goals)) pt''

allPathKeys :: (DsMonad m, MonadReader TypeGraph m) => m (Set (TGV, TGV))
allPathKeys = (Set.flatten . Set.map (\ (t, s) -> Set.map (t,) s)) <$> allKeys

allPathStarts :: forall m. (DsMonad m, MonadReader TypeGraph m) => m (Set TGV)
allPathStarts = Set.map fst <$> allKeys
#else
allPathKeys :: (DsMonad m, MonadReader TypeGraph m) => m (Set (TGV, TGV))
allPathKeys = do
  pathKeys <- allPathStarts
  Set.fromList <$> List.filterM (uncurry goalReachableSimple') [ (g, k) | g <- Foldable.toList pathKeys,
                                                                          k <- Foldable.toList pathKeys ]

allPathStarts :: forall m. (DsMonad m, MonadReader TypeGraph m) => m (Set TGV)
allPathStarts = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- view graph
  kernel <- view typeInfo >>= \ti -> runReaderT (Traversable.mapM expandType (view startTypes ti) >>= Traversable.mapM typeVertex') ti
  let kernel' = mapMaybe kf kernel
  let keep = Set.fromList $ concatMap (reachable g) kernel'
      keep' = Set.map (\(_, key, _) -> key) . Set.map vf $ keep
  return keep'
#endif

reachableFrom :: forall m. (DsMonad m, MonadReader TypeGraph m) => TGV -> m (Set TGV)
reachableFrom v = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- view graph
  case kf v of
    Nothing -> return Set.empty
    Just v' -> return $ Set.map (\(_, key, _) -> key) . Set.map vf $ Set.fromList $ reachable (transposeG g) v'

reachableFromSimple :: forall m. (DsMonad m, MonadReader TypeGraph m) => TGVSimple -> m (Set TGVSimple)
reachableFromSimple v = do
  -- (g, vf, kf) <- graphFromMap <$> view edges
  (g, vf, kf) <- view gsimple
  case kf v of
    Nothing -> return Set.empty
    Just v' -> return $ Set.map (\(_, key, _) -> key) . Set.map vf $ Set.fromList $ reachable (transposeG g) v'

-- | Can we reach the goal type from the start type in this key?
goalReachableFull :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TGV -> TGV -> m Bool
goalReachableFull gkey key0 = isReachable gkey key0 <$> view graph

goalReachableSimple :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TGVSimple -> TGVSimple -> m Bool
goalReachableSimple gkey key0 = isReachable gkey key0 <$> view gsimple

goalReachableSimple' :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TGV -> TGV -> m Bool
goalReachableSimple' gkey key0 = isReachable (simpleVertex gkey) (simpleVertex key0) <$> view gsimple

isReachable :: TypeGraphVertex key => key -> key -> (Graph, Vertex -> ((), key, [key]), key -> Maybe Vertex) -> Bool
isReachable gkey key0 (g, _vf, kf) = path g (fromJust $ kf key0) (fromJust $ kf gkey)

#if 0
  es <- view edges
  let Just v0 = 
      Just vf = 
  return $ 
  case kf key0 of
    Nothing -> error ("isReachable - unknown key: " ++ pprint' key0)
    Just key -> do
      let gvert = fromMaybe (error $ "Unknown goal type: " ++ pprint' gkey ++ "\n" ++ intercalate "\n  " ("known:" : List.map pprint' (Map.keys es))) (kf gkey)
      -- Can we reach any node whose type matches (ConT gname)?  Fields don't matter.
      return $ path g key gvert
#endif

-- | Return the TGV associated with a particular type,
-- with no field specified.
typeGraphVertex :: (MonadReader TypeGraph m, DsMonad m) => Type -> m TGV
typeGraphVertex typ = do
        typ' <- expandType typ
        ask >>= runReaderT (typeVertex' typ') . view typeInfo
        -- magnify typeInfo $ vertex Nothing typ'

-- | Return the TGV associated with a particular type and field.
typeGraphVertexOfField :: (MonadReader TypeGraph m, DsMonad m) => (Name, Name, Either Int Name) -> Type -> m TGV
typeGraphVertexOfField fld typ = do
        typ' <- expandType typ
        ask >>= runReaderT (fieldVertex fld typ') . view typeInfo
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

--- type Edges = GraphEdges () TGV

-- | Return the set of edges implied by the subtype relationship among
-- a set of types.  This is just the nodes of the type graph.  The
-- type aliases are expanded by the th-desugar package to make them
-- suitable for use as map keys.
typeGraphEdges'
    :: forall m. (DsMonad m, MonadReader TypeGraph m, HasSet TGV m) =>
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
    -> m (GraphEdges () TGV)
typeGraphEdges' augment types = do
  execStateT (mapM_ (\typ -> typeGraphVertex typ >>= doNode) types) (mempty :: GraphEdges () TGV)
    where
      doNode v = do
        s <- lift $ getSet
        when (not (member v s)) $
             do lift $ modifySet (insert v)
                doNode' v
      doNode' :: TGV -> StateT (GraphEdges () TGV) m ()
      doNode' typ = do
        addNode typ
        vs <- lift $ augment typ
        mapM_ (addEdge typ) (Set.toList vs)
        mapM_ doNode (Set.toList vs)

      addNode :: TGV -> StateT (GraphEdges () TGV) m ()
      addNode a = modify $ Map.alter (maybe (Just (def, Set.empty)) Just) a

      addEdge :: TGV -> TGV -> StateT (GraphEdges () TGV) m ()
      addEdge a b = modify $ Map.update (\(lbl, s) -> Just (lbl, Set.insert b s)) a

-- | Return the set of adjacent vertices according to the default type
-- graph - i.e. the one determined only by the type definitions, not
-- by any additional hinting function.
adjacent :: forall m. (MonadReader TypeGraph m, DsMonad m) => TGV -> m (Set TGV)
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
makeTypeGraph :: (DsMonad m) => ReaderT TypeInfo m (GraphEdges () TGV) -> TypeInfo -> m TypeGraph
makeTypeGraph makeTypeGraphEdges ti = do
  -- ti <- typeInfo st
  es <- runReaderT makeTypeGraphEdges ti
  return $ TypeGraph
             { _typeInfo = ti
             , _edges = es
             , _graph = graphFromMap es
             , _gsimple = graphFromMap (simpleEdges es)
             , _stack = []
             }
