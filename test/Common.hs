{-# LANGUAGE FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TemplateHaskell #-}
module Common where

import Control.Applicative ((<$>))
import Control.Lens (view)
import Control.Monad.Readers (MonadReaders, ReaderT)
import Control.Monad.States (MonadStates)
import Data.Default (Default)
import Data.List as List (intercalate, map)
import Data.Map as Map (Map, filter, fromList, fromListWith, keys, toList)
import Data.Monoid ((<>), Monoid(mempty, mappend))
import Data.Set as Set (Set, difference, empty, fromList, map, null, toList, union)
import Data.Generics (Data, everywhere, mkT)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.TypeGraph.Edges (GraphEdges)
import Language.Haskell.TH.TypeGraph.Expand (E, unE, ExpandMap)
import Language.Haskell.TH.TypeGraph.Edges (typeGraphEdges)
import Language.Haskell.TH.TypeGraph.Prelude (pprint1)
import Language.Haskell.TH.TypeGraph.Shape (Field)
import Language.Haskell.TH.TypeGraph.TypeInfo (TypeInfo)
import Language.Haskell.TH.TypeGraph.Vertex (etype, syns, TGV, TGV', TGVSimple, TypeGraphVertex, vsimple)

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

-- pprint' :: (Data a, Ppr a) => a -> String
-- pprint' = pprint' . unReify

pprintDec :: Dec -> String
pprintDec = pprint1 . unReify

pprintType :: E Type -> String
pprintType = pprint1 . unReify . view unE

pprintVertex :: (Ppr v, Data v) => v -> String
pprintVertex = pprint1

pprintPred :: E Pred -> String
pprintPred = pprint1 . unReify . view unE

edgesToStrings :: (TypeGraphVertex v, Ppr v, Data v) => GraphEdges v -> [(String, Set String)]
edgesToStrings mp = List.map (\ (t, s) -> (pprintVertex t, Set.map pprintVertex s)) (Map.toList mp)

-- | Return a mapping from vertex to all the known type synonyms for
-- the type in that vertex.
typeSynonymMap :: forall m. (DsMonad m, MonadReaders TypeInfo m, MonadStates ExpandMap m) =>
                  m (Map TGV' (Set Name))
typeSynonymMap =
     (Map.filter (not . Set.null) .
      Map.fromList .
      List.map (\node -> (node, view (vsimple . syns) node)) .
      Map.keys) <$> (typeGraphEdges :: m (GraphEdges TGV'))

-- | Like 'typeSynonymMap', but with all field information removed.
typeSynonymMapSimple :: forall m. (DsMonad m, MonadReaders TypeInfo m, MonadStates ExpandMap m) =>
                        m (Map (E Type) (Set Name))
typeSynonymMapSimple =
    simplify <$> typeSynonymMap
    where
      simplify :: Map TGV' (Set Name) -> Map (E Type) (Set Name)
      simplify mp = Map.fromListWith Set.union (List.map (\ (k, a) -> (view (vsimple . etype) k, a)) (Map.toList mp))
