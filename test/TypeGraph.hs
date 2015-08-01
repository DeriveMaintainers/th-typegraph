{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module TypeGraph where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>))
#endif
import Control.Lens
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (evalStateT)
import Data.List as List (map)
import Data.Map as Map (Map, empty, fromList, keys)
import Data.Set as Set (fromList, singleton)
import Language.Haskell.TH
import Language.Haskell.TH.TypeGraph.Arity (typeArity)
import Language.Haskell.TH.TypeGraph.Edges (dissolveM, simpleEdges)
import Language.Haskell.TH.TypeGraph.Expand (expandType, runExpanded, E(E))
import Language.Haskell.TH.TypeGraph.Free (freeTypeVars)
import Language.Haskell.TH.TypeGraph.TypeInfo (makeTypeInfo, synonyms, typeVertex')
import Language.Haskell.TH.TypeGraph.Vertex (TGV(..), TGVSimple(..), etype)
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
     $([t|String|] >>= \string -> makeTypeInfo (const $ return mempty) [string] >>= lift . view synonyms) `shouldBe` (Map.fromList [(E (AppT ListT (ConT ''Char)), Set.singleton ''String)])

  it "records a type synonym 2" $ do
     $([t|String|] >>= \string ->
       flip evalStateT (Map.empty :: Map Type (E Type))
                (makeTypeInfo (const $ return mempty) [string] >>=
                 runReaderT (expandType string >>= typeVertex')) >>= lift)
          `shouldBe` (TGV {_field = Nothing, _vsimple = TGVSimple {_syns = singleton ''String, _etype = E (AppT ListT (ConT ''Char))}})

  it "can build the TypeInfoGraph for Type" $ do
    $(runQ [t|Type|] >>= \typ -> makeTypeInfo (const $ return mempty) [typ] >>= lift . pprint) `shouldBe` typeInfoOfType

  it "can find the edges of the (simplified) subtype graph of Type (typeEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $ flip evalStateT (Map.empty :: Map Type (E Type)) $
                                      runQ [t|Type|] >>= \typ ->
                                      makeTypeInfo (const $ return mempty) [typ] >>= runReaderT typeGraphEdges' >>= return . simpleEdges >>=
                                      runQ . lift . edgesToStrings)) simpleTypeEdges
        `shouldBe` noDifferences

  it "can find the edges of the (unsimplified) subtype graph of Type (typeEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $ flip evalStateT (Map.empty :: Map Type (E Type)) $
                                runQ [t|Type|] >>= \typ ->
                                makeTypeInfo (const $ return mempty) [typ] >>= runReaderT typeGraphEdges' >>=
                                runQ . lift . edgesToStrings)) typeEdges
        `shouldBe` noDifferences

  it "can find the subtypesOfType" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $ flip evalStateT (Map.empty :: Map Type (E Type)) $
                                  runQ [t|Type|] >>= \typ ->
                                  makeTypeInfo (const $ return mempty) [typ] >>= runReaderT typeGraphEdges' >>=
                                  runQ . lift . List.map pprintVertex . Map.keys)) subtypesOfType
        `shouldBe` noDifferences

  it "can find the edges of the arity 0 subtype graph of Type (arity0TypeEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $ flip evalStateT (Map.empty :: Map Type (E Type)) $
                                runQ [t|Type|] >>= \typ ->
                                makeTypeInfo (const $ return mempty) [typ] >>= runReaderT typeGraphEdges' >>= return . simpleEdges >>=
                                dissolveM (\ v -> (/= 0) <$> (typeArity . runExpanded . view etype) v) >>=
                                runQ . lift . edgesToStrings)) arity0TypeEdges
        `shouldBe` noDifferences
#if 0
  it "can find the edges of the simple subtype graph of Dec (decEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                makeTypeInfo (const $ return mempty) [typ] >>= runReaderT typeGraphEdges' >>= return . simpleEdges >>=
                                runQ . lift . edgesToStrings)) decEdges
        `shouldBe` noDifferences

  it "can find the edges of the arity 0 subtype graph of Dec (arity0DecEdges)" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                makeTypeInfo (const $ return mempty) [typ] >>= runReaderT typeGraphEdges' >>= return . simpleEdges >>=
                                dissolveM (\ v -> (/= 0) <$> (typeArity . runExpanded . _etype) v) >>=
                                runQ . lift . edgesToStrings)) arity0DecEdges
        `shouldBe` noDifferences

  it "can find the subtypesOfDec" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                makeTypeInfo (const $ return mempty) [typ] >>= runReaderT typeGraphVertices >>=
                                runQ . lift . List.map pprint . Set.toList . Set.map simpleVertex)) subtypesOfDec
        `shouldBe` noDifferences

  it "can find the arity0SubtypesOfDec" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                makeTypeInfo (const $ return mempty) [typ] >>= runReaderT typeGraphVertices >>=
                                return . Set.toList . Set.map simpleVertex >>=
                                filterM (\ t -> typeArity (runExpanded (_etype t)) >>= \ a -> return (a == 0)) >>=
                                runQ . lift . List.map pprint)) arity0SubtypesOfDec
        `shouldBe` noDifferences

  it "can find the simpleSubtypesOfDec" $ do
     setDifferences (Set.fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                makeTypeInfo (const $ return mempty) [typ] >>= runReaderT typeGraphVertices >>=
                                runQ . lift . List.map pprint . Set.toList . Set.map simpleVertex)) simpleSubtypesOfDec
        `shouldBe` noDifferences

  it "can find the type synonyms in Dec (decTypeSynonyms)" $ do
     $(withLocalDeclarations [] $
       runQ [t|Dec|] >>= \typ -> makeTypeInfo (const $ return mempty) [typ] >>= runReaderT (typeSynonymMapSimple >>= runQ . lift)) `shouldBe` decTypeSynonyms
#endif

  it "can find the free type variable names in: Map k a" $ do
    $(runQ (appT (appT (conT ''Map) (varT (mkName "k"))) (varT (mkName "a"))) >>= freeTypeVars >>= runQ . lift . show) `shouldBe` "fromList [a,k]"

  it "can find the free type variable names in: Map Int String" $ do
    $(runQ [t|Map Int String|] >>= freeTypeVars  >>= runQ . lift . show) `shouldBe` "fromList []"
