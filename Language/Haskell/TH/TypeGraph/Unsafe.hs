-- | Degenerate instances of Expanded that must be explicitly imported
-- if you want to use them.  They are fine for simple uses of
-- expandType, but not if you are trying to use the return value of
-- expandType as a Map key.

{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Haskell.TH.TypeGraph.Unsafe () where

import Language.Haskell.TH.TypeGraph.Expand (Expanded(markExpanded, runExpanded'))
import Language.Haskell.TH (Type)

#if !MIN_VERSION_template_haskell(2,10,0)
import Language.Haskell.TH (Pred)

instance Expanded Pred Pred where
    markExpanded = id
    runExpanded' = id
#endif

instance Expanded Type Type where
    markExpanded = id
    runExpanded' = id
