-- | Degenerate instances of Expanded that must be explicitly imported
-- if you want to use them.  They are fine for simple uses of
-- expandType, but not if you are trying to use the return value of
-- expandType as a Map key.

{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Haskell.TH.TypeGraph.ExpandUnsafe () where

import Language.Haskell.TH.TypeGraph.Expand (Expanded(markExpanded, runExpanded'))
import Language.Haskell.TH (Type)

instance Expanded Type Type where
    markExpanded = id
    runExpanded' = id
