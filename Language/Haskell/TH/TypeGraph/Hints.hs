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
    ( SinkType
    , VertexHint(..)
    , HasVertexHints(hasVertexHints)
    , vertexHintTypes
    ) where

import Data.Default (Default(def))
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (hcat, ptext)
import Language.Haskell.TH.Syntax (Lift(lift))

-- | If a type is an instance of this class no paths that lead to the
-- internal stucture of the value will be created - the value is
-- considered atomic.
class SinkType a

-- | When a VertexHint value is associated with a Type it describes
-- alterations in the type graph from the usual default.
data VertexHint
    = Normal          -- ^ normal case
    | Hidden          -- ^ don't create this vertex, no in or out edges
    | Divert Type     -- ^ replace all out edges with an edge to an alternate type
    | Extra Type      -- ^ add an extra out edge to the given type
    deriving (Eq, Ord, Show)

instance Default VertexHint where
    def = Normal

instance Lift VertexHint where
    lift Normal = [|Normal|]
    lift Hidden = [|Hidden|]
    lift (Divert x) = [|Divert $(lift x)|]
    lift (Extra x) = [|Extra $(lift x)|]

instance Ppr VertexHint where
    ppr Normal = ptext "Normal"
    ppr Hidden = ptext "Hidden"
    ppr (Divert x) = hcat [ptext "Divert (", ppr x, ptext ")"]
    ppr (Extra x) = hcat [ptext "Extra (", ppr x, ptext ")"]

vertexHintTypes :: VertexHint -> [Type]
vertexHintTypes (Divert x) = [x]
vertexHintTypes (Extra x) = [x]
vertexHintTypes _ = []

class HasVertexHints hint where
    hasVertexHints :: DsMonad m => hint -> m [VertexHint]

instance HasVertexHints VertexHint where
    hasVertexHints h = return [h]
