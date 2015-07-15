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
    , cutEdgesM
    , isolate
    , isolateM
    , link
    , linkM
    , dissolve
    , dissolveM
    , simpleEdges
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>))
import Data.Monoid (mempty)
#endif
import Control.Lens -- (makeLenses, view)
import Control.Monad (filterM)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (execStateT, modify, StateT)
import Data.Default (Default(def))
import Data.Foldable
import Data.List as List (filter, intercalate, map)
import Data.Map as Map ((!), alter, delete, filterWithKey, fromList, keys, lookup, map, Map, mapKeysWith, mapWithKey)
import qualified Data.Map as Map (toList)
import Data.Maybe (mapMaybe)
import Data.Monoid ((<>))
import Data.Set as Set (delete, empty, filter, insert, map, member, fromList, Set, singleton, toList, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.TypeGraph.Expand (E(E), expandType)
import Language.Haskell.TH.TypeGraph.Info (TypeInfo, infoMap, typeSet, allVertices, vertex)
import Language.Haskell.TH.TypeGraph.Prelude (pprint')
import Language.Haskell.TH.TypeGraph.Vertex (simpleVertex, TypeGraphVertex)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Prelude hiding (foldr, mapM_, null)

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
                       (\(k, (_, ks)) -> intercalate "\n    " ((pprint' k ++ " ->" ++ if null ks then " []" else "") : List.map pprint' (Set.toList ks)))
                       (Map.toList x))

-- | Isolate and remove matching nodes
cut :: (Eq a, Ord a) => (a -> Bool) -> GraphEdges node a -> GraphEdges node a
cut p edges = Map.filterWithKey (\v _ -> not (p v)) (isolate p edges)

-- | Monadic predicate version of 'cut'.
cutM :: (Functor m, Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges node a -> m (GraphEdges node a)
cutM victim edges = do
  victims <- Set.fromList <$> filterM victim (Map.keys edges)
  return $ cut (flip Set.member victims) edges

cutEdges :: (Eq a, Ord a) => (a -> a -> Bool) -> GraphEdges node a -> (GraphEdges node a)
cutEdges p edges = Map.mapWithKey (\key (hint, gkeys) -> (hint, Set.filter (\gkey -> not (p key gkey)) gkeys)) edges

cutEdgesM :: (Monad m, Eq a, Ord a) => (a -> a -> m Bool) -> GraphEdges node a -> m (GraphEdges node a)
cutEdgesM p edges = do
  let pairs = Map.toList edges
  ss <- mapM (\(a, (_, s)) -> filterM (\b -> not <$> p a b) (Set.toList s)) pairs
  let pairs' = List.map (\ ((a, (h, _)), s') -> (a, (h, Set.fromList s'))) (zip pairs ss)
  return $ Map.fromList pairs'

-- | Remove all the in- and out-edges of matching nodes
isolate :: (Eq a, Ord a) => (a -> Bool) -> GraphEdges node a -> GraphEdges node a
isolate p edges = cutEdges (\ a b -> p a || p b) edges

-- | Monadic predicate version of 'isolate'.
isolateM :: (Functor m, Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges node a -> m (GraphEdges node a)
isolateM victim edges = do
  victims <- Set.fromList <$> filterM victim (Map.keys edges)
  return $ isolate (flip Set.member victims) edges

-- | Replace the out set of selected nodes
link :: (Eq a, Ord a) => (a -> Maybe (Set a)) -> GraphEdges node a -> GraphEdges node a
link f edges =
    foldr link1 edges (List.map (\a -> (a, f a)) (Map.keys edges))
    where
      link1 :: (Eq a, Ord a) => (a, Maybe (Set a)) -> GraphEdges node a -> GraphEdges node a
      link1 (_, Nothing) edges' = edges'
      link1 (a, Just s) edges' = Map.alter (\(Just (node, _)) -> Just (node, s)) a edges'

linkM :: (Eq a, Ord a, Monad m) => (a -> m (Maybe (Set a))) -> GraphEdges node a -> m (GraphEdges node a)
linkM f edges = do
  let ks = Map.keys edges
  mss <- mapM f ks
  let mp = Map.fromList $ mapMaybe (\(k, ms) -> maybe Nothing (Just .(k,)) ms) $ zip ks mss
  return $ link (\k -> Map.lookup k mp) edges

-- | Remove matching nodes and extend each of their in-edges to each of
-- their out-edges.
dissolve :: (Eq a, Ord a) => (a -> Bool) -> GraphEdges node a -> GraphEdges node a
dissolve p edges =
    foldr dissolve1 edges (List.filter p (Map.keys edges))
    where
      -- Remove a victim and call dissolve1' to extend the edges of each
      -- node that had it in its out set.
      dissolve1 v es = maybe es (\(_, s) -> dissolve1' v (Set.delete v s) (Map.delete v es)) (Map.lookup v es)
      -- If a node's out edges include the victim replace them with next.
      dissolve1' v vs es = Map.map (\(h, s) -> (h, if Set.member v s then Set.union vs (Set.delete v s) else s)) es

-- | Monadic predicate version of 'dissolve'.
dissolveM :: (Functor m, Monad m, Eq a, Ord a) => (a -> m Bool) -> GraphEdges node a -> m (GraphEdges node a)
dissolveM victim edges = do
  victims <- Set.fromList <$> filterM victim (Map.keys edges)
  return $ dissolve (flip Set.member victims) edges

-- | Simplify a graph by throwing away the field information in each
-- node.  This means the nodes only contain the fully expanded Type
-- value (and any type synonyms.)
simpleEdges :: Monoid node => GraphEdges node TypeGraphVertex -> GraphEdges node TypeGraphVertex
simpleEdges = Map.mapWithKey (\v (n, s) -> (n, Set.delete v s)) .    -- delete any self edges
              Map.mapKeysWith combine simpleVertex .   -- simplify each vertex
              Map.map (over _2 (Set.map simpleVertex)) -- simplify the out edges
    where
      combine (n1, s1) (n2, s2) = (n1 <> n2, Set.union s1 s2)
