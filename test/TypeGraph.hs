{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module TypeGraph where

import Control.Applicative ((<$>))
import Control.Lens
import Data.List as List (map)
import Data.Map as Map ((!), fromList)
import Data.Set as Set (fromList, singleton, toList)
import Language.Haskell.TH
import Language.Haskell.TH.TypeGraph.Core (typeArity)
import Language.Haskell.TH.TypeGraph.Expand (runExpanded, E(E))
import Language.Haskell.TH.TypeGraph.Graph (mergeVerticesM {-filterVerticesM, extendEdges, mapVerticesM-})
import Language.Haskell.TH.TypeGraph.Info (typeGraphInfo, synonyms, withTypeGraphInfo, expanded)
import Language.Haskell.TH.TypeGraph.Monad (typeGraphVertices, typeGraphEdges, typeVertex, simpleEdges)
import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex(..))
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common
import Values

tests :: SpecM () ()
tests = do

  it "records a type synonym 1" $ do
     $([t|String|] >>= \ string -> typeGraphInfo [] [string] >>= lift . view synonyms) `shouldBe` (Map.fromList [(E (AppT ListT (ConT ''Char)), Set.singleton ''String)])

  it "records a type synonym 2" $ do
     $([t|String|] >>= \ string -> withTypeGraphInfo [] [string] (view expanded >>= \em -> typeVertex (em ! string)) >>= lift) `shouldBe` (TypeGraphVertex Nothing (singleton ''String) (E (AppT ListT (ConT ''Char))))

  it "can build the TypeInfoGraph for Type" $ do
    $(runQ [t|Type|] >>= \typ -> typeGraphInfo [] [typ] >>= lift . pprint) `shouldBe` typeGraphInfoOfType

  it "can find the edges of the (simplified) subtype graph of Type (typeEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Type|] >>= \typ ->
                                withTypeGraphInfo [] [typ] typeGraphEdges >>= return . simpleEdges >>=
                                runQ . lift . edgesToStrings)) simpleTypeEdges
        `shouldBe` noDifferences

  it "can find the edges of the (unsimplified) subtype graph of Type (typeEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Type|] >>= \typ ->
                                withTypeGraphInfo [] [typ] typeGraphEdges >>=
                                runQ . lift . edgesToStrings)) typeEdges
        `shouldBe` noDifferences

  it "can find the subtypesOfType" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                  runQ [t|Type|] >>= \typ ->
                                  withTypeGraphInfo [] [typ] typeGraphVertices >>=
                                  runQ . lift . List.map pprintVertex . Set.toList)) subtypesOfType
        `shouldBe` noDifferences

  it "can find the edges of the arity 0 subtype graph of Type (arity0TypeEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Type|] >>= \typ ->
                                withTypeGraphInfo [] [typ] typeGraphEdges >>= return . simpleEdges >>=
                                mergeVerticesM (\ v -> (== 0) <$> (typeArity . runExpanded . _etype) v) >>=
                                runQ . lift . edgesToStrings)) arity0TypeEdges
        `shouldBe` noDifferences
#if 0
  it "can find the edges of the simple subtype graph of Dec (decEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                withTypeGraphInfo [] [typ] typeGraphEdges >>= return . simpleEdges >>=
                                runQ . lift . edgesToStrings)) decEdges
        `shouldBe` noDifferences

  it "can find the edges of the arity 0 subtype graph of Dec (arity0DecEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                withTypeGraphInfo [] [typ] typeGraphEdges >>= return . simpleEdges >>=
                                mergeVerticesM (\ v -> (== 0) <$> (typeArity . runExpanded . _etype) v) >>=
                                runQ . lift . edgesToStrings)) arity0DecEdges
        `shouldBe` noDifferences

  it "can find the subtypesOfDec" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                withTypeGraphInfo [] [typ] typeGraphVertices >>=
                                runQ . lift . List.map pprint . Set.toList . Set.map simpleVertex)) subtypesOfDec
        `shouldBe` noDifferences

  it "can find the arity0SubtypesOfDec" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                withTypeGraphInfo [] [typ] typeGraphVertices >>=
                                return . Set.toList . Set.map simpleVertex >>=
                                filterM (\ t -> typeArity (runExpanded (_etype t)) >>= \ a -> return (a == 0)) >>=
                                runQ . lift . List.map pprint)) arity0SubtypesOfDec
        `shouldBe` noDifferences

  it "can find the simpleSubtypesOfDec" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                withTypeGraphInfo [] [typ] typeGraphVertices >>=
                                runQ . lift . List.map pprint . Set.toList . Set.map simpleVertex)) simpleSubtypesOfDec
        `shouldBe` noDifferences

  it "can find the type synonyms in Dec (decTypeSynonyms)" $ do
     $(withLocalDeclarations [] $
       runQ [t|Dec|] >>= \typ -> withTypeGraphInfo [] [typ] (typeSynonymMapSimple >>= runQ . lift)) `shouldBe` decTypeSynonyms
#endif
