{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import Control.DeepSeq
import Control.Monad.State (evalStateT, runStateT)
import Data.Array.Base
import Data.ByteString (ByteString)
import Data.List as List (intercalate, map, null)
import Data.Map as Map (Map, fromList, toList, map, mapKeys, empty)
import Data.Set as Set (Set, fromList, toList, null, difference, empty)
import Data.Text (Text)
import Data.Monoid (mempty)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.ReifyMany
import Language.Haskell.TH.Syntax (Lift(lift), Quasi(qReifyInstances))
import System.Exit (ExitCode)
import Test.Hspec hiding (runIO)
import TypeGraph (tests)

main :: IO ()
main = hspec $ do
  TypeGraph.tests
