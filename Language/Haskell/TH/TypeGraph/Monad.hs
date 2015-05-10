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
module Language.Haskell.TH.TypeGraph.Monad
    ( findEdges
    , typeVertex
    , fieldVertex
    -- , typeVertices
    , typeGraphEdges
    , typeGraphVertices
    , typeGraph
    , simpleEdges
    , simpleVertex
    , typeSynonymMap
    , typeSynonymMapSimple
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
import Data.Monoid (mempty)
#endif
import Control.Lens -- (makeLenses, view)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (execStateT, modify, StateT)
import Data.Graph (Graph, Vertex)
import Data.List as List (map)
import Data.Map as Map ((!), filter, findWithDefault, fromList, fromListWith,
                        keys, Map, map, mapKeys, mapWithKey, toList, alter)
import Data.Maybe (fromMaybe)
import Data.Set as Set (delete, empty, fromList, insert, map, null, Set, singleton, toList, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.TypeGraph.Expand (E(E))
import Language.Haskell.TH.TypeGraph.Graph (cutVertex, GraphEdges, graphFromMap)
import Language.Haskell.TH.TypeGraph.Edges (TypeGraphEdges)
import Language.Haskell.TH.TypeGraph.Hints (VertexHint(..))
import Language.Haskell.TH.TypeGraph.Info (TypeGraphInfo, expanded, fields, hints, infoMap, synonyms, typeSet)
import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex(..), etype, field)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()

-- | Build a TypeGraphVertex from an unexpanded type.
typeVertex :: MonadReader TypeGraphInfo m => E Type -> m TypeGraphVertex
typeVertex etyp = do
  sm <- view synonyms
  return $ TypeGraphVertex {_field = Nothing, _syns = Map.findWithDefault Set.empty etyp sm, _etype = etyp}

-- | Build a TypeGraphVertex for a field of a record.  This calls
-- 'typeVertex' and then sets the _field value.
fieldVertex :: MonadReader TypeGraphInfo m => E Type -> (Name, Name, Either Int Name) -> m TypeGraphVertex
fieldVertex typ fld = typeVertex typ >>= \vertex -> return $ vertex {_field = Just fld}

-- | Return the set of vertices referred to by a hint's vertex - if
-- field is Nothing it means all the fields with that type, if it is
-- something it means just itself.
fieldVertices :: MonadReader TypeGraphInfo m => TypeGraphVertex -> m (Set TypeGraphVertex)
fieldVertices v =
    case view field v of
      Just _ -> return $ singleton v
      Nothing -> do
        fm <- view fields
        let fs = Map.findWithDefault Set.empty (view etype v) fm
            vs = Set.map (\fld -> set field (Just fld) v) fs
        return $ Set.insert v vs

-- | Start with the type graph on the known types with no field
-- information, and build a new graph which incorporates the
-- information from the vertex hints.  This means splitting the nodes
-- according to record fields, because hints can refer to particular
-- fields of a record.
typeGraphEdges :: forall m. MonadReader TypeGraphInfo m => m TypeGraphEdges
typeGraphEdges = do
  findEdges >>= execStateT (view hints >>= mapM doHint')
    where
      doHint' :: (TypeGraphVertex, VertexHint) -> StateT TypeGraphEdges m ()
      doHint' (v, h) = do
        doHint v h

      doHint :: TypeGraphVertex -> VertexHint -> StateT TypeGraphEdges m ()
      doHint v Sink = fieldVertices v >>= mapM_ (modify . Map.alter (\_ -> Just Set.empty)) . Set.toList
      doHint _ Normal = return ()
      doHint v Hidden = fieldVertices v >>= mapM_ (modify . cutVertex) . Set.toList
      doHint v (Divert typ) = do
        em <- view expanded
        v' <- typeVertex (em ! typ)
        fieldVertices v >>= mapM_ (modify . Map.alter (\_ -> Just (singleton v'))) . Set.toList
      doHint v (Extra typ) = do
        em <- view expanded
        v' <- typeVertex (em ! typ)
        fieldVertices v >>= mapM_ (modify . Map.alter (\ mvs -> Just (Set.insert v' (fromMaybe Set.empty mvs)))) . Set.toList

-- | Find all the 'TypeGraphVertex' that involve this type.  All
-- returned nodes will have the same set of type synonyms, but there
-- will be one for each field where the type appears and one with
-- field Nothing.
typeVertices :: MonadReader TypeGraphInfo m => E Type -> m (Set TypeGraphVertex)
typeVertices typ = do
  syns <- view synonyms >>= return . Map.findWithDefault Set.empty typ
  flds <- view fields >>= return . Set.insert Nothing . Set.map Just . Map.findWithDefault Set.empty typ
  return $ Set.map (\ f -> TypeGraphVertex {_etype = typ, _syns = syns, _field = f}) flds

-- | Given the discovered set of types and maps of type synonyms and
-- fields, build and return the GraphEdges relation on TypeGraphVertex.
-- This is not a recursive function, it stops when it reaches the field
-- types.
findEdges :: forall m. (MonadReader TypeGraphInfo m) =>
             m (GraphEdges TypeGraphVertex)
findEdges = do
  execStateT (view typeSet >>= \ts -> mapM_ doType (Set.toList ts)) mempty
    where
      doType :: Type -> StateT (GraphEdges TypeGraphVertex) m ()
      doType typ = view expanded >>= \em -> typeVertex (em ! typ) >>= doVertex

      doVertex :: TypeGraphVertex -> StateT (GraphEdges TypeGraphVertex) m ()
      doVertex v = do
        vs <- fieldVertices v
        mapM_ node (Set.toList vs)
        case view etype v of
          E (ConT tname) -> view infoMap >>= \ mp -> doInfo vs (mp ! tname)
          E (AppT typ1 typ2) -> do
            v1 <- typeVertex (E typ1)
            v2 <- typeVertex (E typ2)
            mapM_ (flip edge v1) (Set.toList vs)
            mapM_ (flip edge v2) (Set.toList vs)
            doVertex v1
            doVertex v2
          _ -> return ()

      doInfo :: Set TypeGraphVertex -> Info -> StateT (GraphEdges TypeGraphVertex) m ()
      doInfo vs (TyConI dec) = doDec vs dec
      -- doInfo vs (PrimTyConI tname _ _) = return ()
      doInfo _ _ = return ()

      doDec :: Set TypeGraphVertex -> Dec -> StateT (GraphEdges TypeGraphVertex) m ()
      doDec _ (TySynD _ _ _) = return () -- This type will be in typeSet
      doDec vs (NewtypeD _ tname _ constr _) = doCon vs tname constr
      doDec vs (DataD _ tname _ constrs _) = mapM_ (doCon vs tname) constrs
      doDec _ _ = return ()

      doCon :: Set TypeGraphVertex -> Name -> Con -> StateT (GraphEdges TypeGraphVertex) m ()
      doCon vs tname (ForallC _ _ con) = doCon vs tname con
      doCon vs tname (NormalC cname flds) = mapM_ (uncurry (doField vs tname cname)) (List.map (\ (n, (_, ftype)) -> (Left n, ftype)) (zip [1..] flds))
      doCon vs tname (RecC cname flds) = mapM_ (uncurry (doField vs tname cname)) (List.map (\ (fname, _, ftype) -> (Right fname, ftype)) flds)
      doCon vs tname (InfixC (_, lhs) cname (_, rhs)) = doField vs tname cname (Left 1) lhs >> doField vs tname cname (Left 2) rhs

      -- Connect the vertex for this record type to one particular field vertex
      doField ::  Set TypeGraphVertex ->Name -> Name -> Either Int Name -> Type -> StateT (GraphEdges TypeGraphVertex) m ()
      doField vs tname cname fld ftyp = do
        em <- view expanded
        v2 <- fieldVertex (em ! ftyp) (tname, cname, fld)
        mapM_ (flip edge v2) (Set.toList vs)
        -- Here's where we don't recurse, see?
        -- doVertex v2

      node v = modify (Map.alter (Just . maybe Set.empty id) v)
      edge v1 v2 = modify (Map.alter (Just . maybe (singleton v2) (Set.insert v2)) v1) >> node v2

-- | Return the set of types embedded in the given type.  This is just
-- the nodes of the type graph.  The type synonymes are expanded by the
-- th-desugar package to make them suitable for use as map keys.
typeGraphVertices :: forall m. (DsMonad m, MonadReader TypeGraphInfo m) => m (Set TypeGraphVertex)
typeGraphVertices = (Set.fromList . Map.keys) <$> typeGraphEdges

-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
typeGraph :: forall m node key. (DsMonad m, MonadReader TypeGraphInfo m, node ~ TypeGraphVertex, key ~ TypeGraphVertex) =>
                m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
typeGraph = graphFromMap <$> typeGraphEdges

-- | Simplify a graph by throwing away the field information in each
-- node.  This means the nodes only contain the fully expanded Type
-- value (and any type synonyms.)
simpleEdges :: TypeGraphEdges -> TypeGraphEdges
simpleEdges = Map.mapWithKey Set.delete . Map.mapKeys simpleVertex . Map.map (Set.map simpleVertex)

simpleVertex :: TypeGraphVertex -> TypeGraphVertex
simpleVertex node = node {_field = Nothing}

-- | Find all the reachable type synonyms and return then in a Map.
typeSynonymMap :: forall m. (DsMonad m, MonadReader TypeGraphInfo m) => m (Map TypeGraphVertex (Set Name))
typeSynonymMap =
     (Map.filter (not . Set.null) .
      Map.fromList .
      List.map (\node -> (node, _syns node)) .
      Map.keys) <$> typeGraphEdges

typeSynonymMapSimple :: forall m. (DsMonad m, MonadReader TypeGraphInfo m) => m (Map (E Type) (Set Name))
typeSynonymMapSimple =
    simplify <$> typeSynonymMap
    where
      simplify :: Map TypeGraphVertex (Set Name) -> Map (E Type) (Set Name)
      simplify mp = Map.fromListWith Set.union (List.map (\ (k, a) -> (_etype k, a)) (Map.toList mp))
