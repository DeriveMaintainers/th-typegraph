{-# LANGUAGE FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TemplateHaskell #-}
module Common where

import Control.Applicative ((<$>))
import Control.Monad.Reader (MonadReader, ReaderT)
import Data.Default (Default)
import Data.List as List (intercalate, map)
import Data.Map as Map (Map, filter, fromList, fromListWith, keys, toList)
import Data.Monoid ((<>), Monoid(mempty, mappend))
import Data.Set as Set (Set, difference, empty, fromList, null, toList, union)
import Data.Generics (Data, everywhere, mkT)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.TypeGraph.Edges (GraphEdges)
import Language.Haskell.TH.TypeGraph.Expand (E, markExpanded, runExpanded)
import Language.Haskell.TH.TypeGraph.Info (TypeInfo, typeInfo)
import Language.Haskell.TH.TypeGraph.Edges (typeGraphEdges)
import Language.Haskell.TH.TypeGraph.Shape (pprint')
import Language.Haskell.TH.TypeGraph.Vertex (Field, TypeGraphVertex(..))

import Language.Haskell.TH.Syntax (Lift(lift))

data SetDifferences a = SetDifferences {unexpected :: Set a, missing :: Set a} deriving (Eq, Ord, Show)

setDifferences :: Ord a => Set a -> Set a -> SetDifferences a
setDifferences actual expected = SetDifferences {unexpected = Set.difference actual expected, missing = Set.difference expected actual}
noDifferences = SetDifferences {unexpected = Set.empty, missing = Set.empty}

unReify :: Data a => a -> a
unReify = everywhere (mkT unReifyName)

unReifyName :: Name -> Name
unReifyName = mkName . nameBase

-- Some very nasty bug is triggered here in ghc-7.8 if we try to implement
-- a generic function that unReifies the symbols.  Ghc-7.10 works fine

-- pprint'' :: (Data a, Ppr a) => a -> String
-- pprint'' = pprint' . unReify

pprintDec :: Dec -> String
pprintDec = pprint' . unReify

pprintType :: E Type -> String
pprintType = pprint' . unReify . runExpanded

pprintVertex :: TypeGraphVertex -> String
pprintVertex = pprint'

pprintPred :: E Pred -> String
pprintPred = pprint' . unReify . runExpanded

edgesToStrings :: GraphEdges label TypeGraphVertex -> [(String, [String])]
edgesToStrings mp = List.map (\ (t, (_, s)) -> (pprintVertex t, map pprintVertex (Set.toList s))) (Map.toList mp)

typeInfo' :: DsMonad m => [Type] -> m TypeInfo
typeInfo' = typeInfo

typeGraphEdges' :: forall m. (DsMonad m, MonadReader TypeInfo m) => m (GraphEdges () TypeGraphVertex)
typeGraphEdges' = typeGraphEdges

-- | Return a mapping from vertex to all the known type synonyms for
-- the type in that vertex.
typeSynonymMap :: forall m. (DsMonad m, MonadReader TypeInfo m) =>
                  m (Map TypeGraphVertex (Set Name))
typeSynonymMap =
     (Map.filter (not . Set.null) .
      Map.fromList .
      List.map (\node -> (node, _syns node)) .
      Map.keys) <$> (typeGraphEdges :: m (GraphEdges () TypeGraphVertex))

-- | Like 'typeSynonymMap', but with all field information removed.
typeSynonymMapSimple :: forall m. (DsMonad m, MonadReader TypeInfo m) =>
                        m (Map (E Type) (Set Name))
typeSynonymMapSimple =
    simplify <$> typeSynonymMap
    where
      simplify :: Map TypeGraphVertex (Set Name) -> Map (E Type) (Set Name)
      simplify mp = Map.fromListWith Set.union (List.map (\ (k, a) -> (_etype k, a)) (Map.toList mp))
