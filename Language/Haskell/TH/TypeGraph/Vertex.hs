{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Haskell.TH.TypeGraph.Vertex
    ( Field
    , TypeGraphVertex(..)
    , field, syns, etype
    , simpleVertex
    , typeNames
    , bestType
    ) where

import Control.Lens -- (makeLenses, view)
import Data.Generics (Data, everywhere, mkT)
import Data.List as List (concatMap, intersperse)
import Data.Map as Map (Map, fromList, toList)
import Data.Set as Set (fromList, insert, minView, Set, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (hcat, ptext)
import Language.Haskell.TH.Syntax (Lift(lift))
import Language.Haskell.TH.TypeGraph.Expand (E(E), markExpanded, runExpanded)

instance Lift a => Lift (Set a) where
    lift s = [|Set.fromList $(lift (Set.toList s))|]

instance (Lift a, Lift b) => Lift (Map a b) where
    lift mp = [|Map.fromList $(lift (Map.toList mp))|]

instance Lift (E Type) where
    lift etype = [|markExpanded $(lift (runExpanded etype))|]

unReify :: Data a => a -> a
unReify = everywhere (mkT unReifyName)

unReifyName :: Name -> Name
unReifyName = mkName . nameBase

type Field = ( Name, -- type name
               Name, -- constructor name
               Either Int -- field position
                      Name -- field name
             )

instance Ppr Field where
    ppr (tname, cname, field) = ptext $
        "field " ++
        show (unReifyName tname) ++ "." ++
        either (\ n -> show (unReifyName cname) ++ "[" ++ show n ++ "]") (\ f -> show (unReifyName f)) field

instance Ppr (Maybe Field, E Type) where
    ppr (mf, typ) = ptext $ pprint typ ++ maybe "" (\fld -> " (field " ++ pprint fld ++ ")") mf

instance Ppr (Maybe Field, Type) where
    ppr (mf, typ) = ptext $ pprint typ ++ " (unexpanded)" ++ maybe "" (\fld -> " (field " ++ pprint fld ++ ")") mf

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
