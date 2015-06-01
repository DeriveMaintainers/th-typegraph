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
module Language.Haskell.TH.TypeGraph.Hints
    ( VertexHint(..)
    , HasVertexHints(hasVertexHints)
    , vertexHintTypes
    ) where

import Data.Default (Default(def))
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax (Lift(lift))

-- | When a VertexHint value is associated with a Type it describes
-- alterations in the type graph from the usual default.
data VertexHint
    = Normal          -- ^ normal case
    deriving (Eq, Ord, Show)

instance Default VertexHint where
    def = Normal

instance Lift VertexHint where
    lift Normal = [|Normal|]

instance Ppr VertexHint where
    ppr Normal = ptext "Normal"

vertexHintTypes :: VertexHint -> [Type]
vertexHintTypes _ = []

class HasVertexHints hint where
    hasVertexHints :: DsMonad m => hint -> m [VertexHint]

instance HasVertexHints VertexHint where
    hasVertexHints h = return [h]
