{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Haskell.TH.TypeGraph.Edges
    ( TypeGraphEdges
    ) where

import Data.List as List (intercalate, map)
import Data.Map as Map (toList)
import Data.Set as Set (toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.TypeGraph.Graph (GraphEdges)
import Language.Haskell.TH.TypeGraph.Core (pprint')
import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (ptext)

type TypeGraphEdges label = GraphEdges label TypeGraphVertex

instance Ppr (TypeGraphEdges label) where
    ppr x =
        ptext $ intercalate "\n  " $
          "edges:" : (List.map
                       (\ (k, (_, ks)) -> intercalate "\n    " ((pprint' k ++ "->") : List.map pprint' (Set.toList ks)))
                       (Map.toList x))
