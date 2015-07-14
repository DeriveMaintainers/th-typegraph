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

    , makeTypeGraph
    , VertexStatus(..)
    , typeGraphEdges'
    , adjacent
    , typeVertex
    , fieldVertex
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
import Data.Monoid (mempty)
#else
import Control.Applicative
#endif
import Control.Lens -- (makeLenses, over, view)
import Control.Monad (when)
import Control.Monad (filterM)
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
import Data.Set as Set (map)
import Data.Set as Set (empty, fromList, insert, member, Set, singleton, toList, unions)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Context (HasSet(getSet, modifySet))
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax (Quasi(..))
import Language.Haskell.TH.TypeGraph.Edges (GraphEdges, simpleEdges)
import Language.Haskell.TH.TypeGraph.Expand (E(E), expandType)
import Language.Haskell.TH.TypeGraph.Info (startTypes, TypeInfo, vertex)
import Language.Haskell.TH.TypeGraph.Stack (HasStack(withStack, push), StackElement(StackElement))
import Language.Haskell.TH.TypeGraph.Vertex (simpleVertex, TypeGraphVertex, etype)
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
  Set.fromList <$> filterM (uncurry goalReachableSimple) [ (g, k) | g <- Foldable.toList (Set.map simpleVertex pathKeys),
                                                                    k <- Foldable.toList (Set.map simpleVertex pathKeys) ]

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

-- | Can we reach the goal type from the start type in this key?
goalReachableFull :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TypeGraphVertex -> TypeGraphVertex -> m Bool
goalReachableFull gkey key0 = isReachable gkey key0 <$> view graph

goalReachableSimple :: (Functor m, DsMonad m, MonadReader TypeGraph m) => TypeGraphVertex -> TypeGraphVertex -> m Bool
goalReachableSimple gkey key0 = isReachable (simpleVertex gkey) (simpleVertex key0) <$> view gsimple

isReachable :: TypeGraphVertex -> TypeGraphVertex -> (Graph, Vertex -> ((), TypeGraphVertex, [TypeGraphVertex]), TypeGraphVertex -> Maybe Vertex) -> Bool
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

-- | Return the TypeGraphVertex associated with a particular type,
-- with no field specified.
typeVertex :: (MonadReader TypeGraph m, DsMonad m) => Type -> m TypeGraphVertex
typeVertex typ = do
        typ' <- expandType typ
        ask >>= runReaderT (vertex Nothing typ') . view typeInfo
        -- magnify typeInfo $ vertex Nothing typ'

-- | Return the TypeGraphVertex associated with a particular type and field.
fieldVertex :: (MonadReader TypeGraph m, DsMonad m) => (Name, Name, Either Int Name) -> Type -> m TypeGraphVertex
fieldVertex fld typ = do
        typ' <- expandType typ
        ask >>= runReaderT (vertex (Just fld) typ') . view typeInfo
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

--- type Edges = GraphEdges () TypeGraphVertex

-- | Return the set of edges implied by the subtype relationship among
-- a set of types.  This is just the nodes of the type graph.  The
-- type aliases are expanded by the th-desugar package to make them
-- suitable for use as map keys.
typeGraphEdges'
    :: forall m. (DsMonad m, MonadReader TypeGraph m, HasSet TypeGraphVertex m) =>
       (TypeGraphVertex -> m (Set TypeGraphVertex))
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
    -> m (GraphEdges () TypeGraphVertex)
typeGraphEdges' augment types = do
  execStateT (mapM_ (\typ -> typeVertex typ >>= doNode) types) (mempty :: GraphEdges () TypeGraphVertex)
    where
      doNode v = do
        s <- lift $ getSet
        when (not (member v s)) $
             do lift $ modifySet (insert v)
                doNode' v
      doNode' :: TypeGraphVertex -> StateT (GraphEdges () TypeGraphVertex) m ()
      doNode' typ = do
        addNode typ
        vs <- lift $ augment typ
        mapM_ (addEdge typ) (Set.toList vs)
        mapM_ doNode (Set.toList vs)

      addNode :: TypeGraphVertex -> StateT (GraphEdges () TypeGraphVertex) m ()
      addNode a = modify $ Map.alter (maybe (Just (def, Set.empty)) Just) a

      addEdge :: TypeGraphVertex -> TypeGraphVertex -> StateT (GraphEdges () TypeGraphVertex) m ()
      addEdge a b = modify $ Map.update (\(lbl, s) -> Just (lbl, Set.insert b s)) a

-- | Return the set of adjacent vertices according to the default type
-- graph - i.e. the one determined only by the type definitions, not
-- by any additional hinting function.
adjacent :: forall m. (MonadReader TypeGraph m, DsMonad m) => TypeGraphVertex -> m (Set TypeGraphVertex)
adjacent typ =
    case view etype typ of
      E (ForallT _ _ typ') -> typeVertex typ' >>= adjacent
      E (AppT c e) ->
          typeVertex c >>= \c' ->
          typeVertex e >>= \e' ->
          return $ Set.fromList [c', e']
      E (ConT name) -> do
        info <- qReify name
        case info of
          TyConI dec -> doDec dec
          _ -> return mempty
      _typ -> return $ {-trace ("Unrecognized type: " ++ pprint' typ)-} mempty
    where
      doDec :: Dec -> m (Set TypeGraphVertex)
      doDec dec@(NewtypeD _ tname _ con _) = doCon tname dec con
      doDec dec@(DataD _ tname _ cns _) = Set.unions <$> mapM (doCon tname dec) cns
      doDec (TySynD _tname _tvars typ') = singleton <$> typeVertex typ'
      doDec _ = return mempty

      doCon :: Name -> Dec -> Con -> m (Set TypeGraphVertex)
      doCon tname dec (ForallC _ _ con) = doCon tname dec con
      doCon tname dec (NormalC cname fields) = Set.unions <$> mapM (doField tname dec cname) (zip (List.map Left ([1..] :: [Int])) (List.map snd fields))
      doCon tname dec (RecC cname fields) = Set.unions <$> mapM (doField tname dec cname) (List.map (\ (fname, _, typ') -> (Right fname, typ')) fields)
      doCon tname dec (InfixC (_, lhs) cname (_, rhs)) = Set.unions <$> mapM (doField tname dec cname) [(Left 1, lhs), (Left 2, rhs)]

      doField :: Name -> Dec -> Name -> (Either Int Name, Type) -> m (Set TypeGraphVertex)
      doField tname _dec cname (fld, ftype) = Set.singleton <$> fieldVertex (tname, cname, fld) ftype

-- FIXME: pass in ti, pass in makeTypeGraphEdges, remove Q, move to TypeGraph.Graph
makeTypeGraph :: (DsMonad m) => ReaderT TypeInfo m (GraphEdges () TypeGraphVertex) -> TypeInfo -> m TypeGraph
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
