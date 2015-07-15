{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Haskell.TH.TypeGraph.Vertex
    ( TypeGraphVertex(..)
    , field, syns, etype
    , simpleVertex
    , typeNames
    , bestType
    ) where

import Control.Lens -- (makeLenses, view)
import Data.List as List (concatMap, intersperse)
import Data.Set as Set (insert, minView, Set, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (hcat, ptext)
import Language.Haskell.TH.Syntax (Lift(lift))
import Language.Haskell.TH.TypeGraph.Expand (E(E), runExpanded)
import Language.Haskell.TH.TypeGraph.Prelude (unReify, unReifyName)
import Language.Haskell.TH.TypeGraph.Shape (Field)

-- | For simple type graphs always set _field and _synonyms to Nothing.
data TypeGraphVertex
    = TypeGraphVertex
      { _field :: Maybe Field -- ^ The record field which contains this type
      , _syns :: Set Name -- ^ All the type synonyms that expand to this type
      , _etype :: E Type -- ^ The fully expanded type
      } deriving (Eq, Ord, Show)

instance Ppr TypeGraphVertex where
    ppr (TypeGraphVertex {_field = fld, _syns = ns, _etype = typ}) =
        hcat (ppr (unReify (runExpanded typ)) :
              case (fld, Set.toList ns) of
                 (Nothing, []) -> []
                 _ ->   [ptext " ("] ++
                        intersperse (ptext ", ")
                          (List.concatMap (\ n -> [ptext ("aka " ++ show (unReifyName n))]) (Set.toList ns) ++
                           maybe [] (\ f -> [ppr f]) fld) ++
                        [ptext ")"])

$(makeLenses ''TypeGraphVertex)

simpleVertex :: TypeGraphVertex -> TypeGraphVertex
simpleVertex v = v {_field = Nothing}

-- | Return the set of 'Name' of a type's synonyms, plus the name (if
-- any) used in its data declaration.  Note that this might return the
-- empty set.
typeNames :: TypeGraphVertex -> Set Name
typeNames (TypeGraphVertex {_etype = E (ConT tname), _syns = s}) = Set.insert tname s
typeNames (TypeGraphVertex {_syns = s}) = s

bestType :: TypeGraphVertex -> Type
bestType (TypeGraphVertex {_etype = E (ConT name)}) = ConT name
bestType v = maybe (let (E x) = view etype v in x) (ConT . fst) (Set.minView (view syns v))

instance Lift TypeGraphVertex where
    lift (TypeGraphVertex {_field = f, _syns = ns, _etype = t}) =
        [|TypeGraphVertex {_field = $(lift f), _syns = $(lift ns), _etype = $(lift t)}|]
