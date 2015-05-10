{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.TH.TypeGraph.Vertex
    ( TypeGraphVertex(..)
    , field, syns, etype
    , typeNames
    , typeVertex -- old
    , fieldVertex -- old
    , oldVertex -- old
    ) where

import Control.Lens -- (makeLenses, view)
import Data.List as List (concatMap, intersperse)
import Data.Set as Set (empty, insert, Set, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (hcat, ptext)
import Language.Haskell.TH.Syntax (Lift(lift))
import Language.Haskell.TH.TypeGraph.Core (Field, unReify, unReifyName)
import Language.Haskell.TH.TypeGraph.Expand (E(E), runExpanded)

-- | For simple type graphs always set _field and _synonyms to Nothing.
data TypeGraphVertex
    = TypeGraphVertex
      { _field :: Maybe (Name, Name, Either Int Name) -- ^ The record filed which contains this type
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

-- | Return the set of 'Name' of a type's synonyms, plus the name (if
-- any) used in its data declaration.  Note that this might return the
-- empty set.
typeNames :: TypeGraphVertex -> Set Name
typeNames (TypeGraphVertex {_etype = E (ConT tname), _syns = s}) = Set.insert tname s
typeNames (TypeGraphVertex {_syns = s}) = s

instance Lift TypeGraphVertex where
    lift (TypeGraphVertex {_field = f, _syns = ns, _etype = t}) =
        [|TypeGraphVertex {_field = $(lift f), _syns = $(lift ns), _etype = $(lift t)}|]

typeVertex :: DsMonad m => Type -> m TypeGraphVertex
typeVertex typ = return $ TypeGraphVertex {_etype = E typ, _field = Nothing, _syns = Set.empty}
fieldVertex :: DsMonad m => Type -> (Name, Name, Either Int Name) -> m TypeGraphVertex
fieldVertex typ fld = return $ TypeGraphVertex {_etype = E typ, _field = Just fld, _syns = Set.empty}

-- Transitional
oldVertex :: DsMonad m => (Maybe Field, Type) -> m TypeGraphVertex
oldVertex (fld, typ) = maybe (typeVertex typ) (fieldVertex typ) fld
