-- | Degenerate instances of Expanded that must be explicitly imported
-- if you want to use them.  They are fine for simple uses of
-- expandType, but not if you are trying to use the return value of
-- expandType as a Map key.

{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Haskell.TH.TypeGraph.Unsafe () where

import Language.Haskell.TH (Pred, Type)
import Language.Haskell.TH.TypeGraph.Expand (Expanded(markExpanded, runExpanded))

instance Expanded Type Type where
    markExpanded = id
    runExpanded = id

#if !MIN_VERSION_template_haskell(2,10,0)
instance Expanded Pred Pred where
    markExpanded = id
    runExpanded = id
#endif
