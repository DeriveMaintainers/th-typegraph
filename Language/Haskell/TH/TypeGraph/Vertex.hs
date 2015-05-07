{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.TH.TypeGraph.Vertex
    ( TypeGraphVertex(..)
    , field, syns, etype
    , typeNames
    ) where

import Control.Lens -- (makeLenses, view)
import Data.Generics (Data, everywhere, mkT)
import Data.List as List (concatMap, intersperse)
import Data.Set as Set (insert, Set, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.TypeGraph.Core ()
import Language.Haskell.TH.TypeGraph.Expand (E(E), runExpanded)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (hcat, ptext)
import Language.Haskell.TH.Syntax (Lift(lift))

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
                           maybe [] (\ f -> [ptext (printField f)]) fld) ++
                        [ptext ")"])
        where
          printField :: (Name, Name, Either Int Name) -> String
          printField (tname, cname, field) =
              "field " ++
              show (unReifyName tname) ++ "." ++
              either (\ n -> show (unReifyName cname) ++ "[" ++ show n ++ "]") (\ f -> show (unReifyName f)) field

          unReify :: Data a => a -> a
          unReify = everywhere (mkT unReifyName)

          unReifyName :: Name -> Name
          unReifyName = mkName . nameBase

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
