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
import Language.Haskell.TH.TypeGraph.Core (Field, pprint')
import Language.Haskell.TH.TypeGraph.Expand (E, markExpanded, runExpanded)
import Language.Haskell.TH.TypeGraph.Graph (GraphEdges)
import Language.Haskell.TH.TypeGraph.Hints (HasVertexHints, VertexHint(..))
import Language.Haskell.TH.TypeGraph.Info (TypeGraphInfo, typeGraphInfo)
import Language.Haskell.TH.TypeGraph.Monad (typeGraphEdges)
import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex(..))

import Language.Haskell.TH.Syntax (Lift(lift))

instance Monoid VertexHint where
    mempty = Normal
    mappend Normal x = x
    mappend x Normal = x
    mappend x@(Divert _) _ = x
    mappend _ x@(Divert _) = x
    mappend x _ = x

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

typeGraphInfo' :: DsMonad m => [(Maybe Field, Name, VertexHint)] -> [Type] -> m (TypeGraphInfo VertexHint)
typeGraphInfo' = typeGraphInfo

typeGraphEdges' :: forall m. (DsMonad m, MonadReader (TypeGraphInfo VertexHint) m) => m (GraphEdges VertexHint TypeGraphVertex)
typeGraphEdges' = typeGraphEdges

-- | Return a mapping from vertex to all the known type synonyms for
-- the type in that vertex.
typeSynonymMap :: forall m hint. (DsMonad m, Default hint, Eq hint, HasVertexHints hint, MonadReader (TypeGraphInfo hint) m) =>
                  m (Map TypeGraphVertex (Set Name))
typeSynonymMap =
     (Map.filter (not . Set.null) .
      Map.fromList .
      List.map (\node -> (node, _syns node)) .
      Map.keys) <$> typeGraphEdges

-- | Like 'typeSynonymMap', but with all field information removed.
typeSynonymMapSimple :: forall m hint. (DsMonad m, Default hint, Eq hint, HasVertexHints hint, MonadReader (TypeGraphInfo hint) m) =>
                        m (Map (E Type) (Set Name))
typeSynonymMapSimple =
    simplify <$> typeSynonymMap
    where
      simplify :: Map TypeGraphVertex (Set Name) -> Map (E Type) (Set Name)
      simplify mp = Map.fromListWith Set.union (List.map (\ (k, a) -> (_etype k, a)) (Map.toList mp))
