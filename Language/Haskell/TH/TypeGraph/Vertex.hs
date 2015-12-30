{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Haskell.TH.TypeGraph.Vertex
    ( TypeGraphVertex(..)
    , TGV(..), field, vsimple
    , TGVSimple(..), syns, etype
    , tgv
    ) where

import Control.Lens
import Data.Data (Data)
import Data.List as List (concatMap, intersperse)
import Data.Map as Map (Map, toList)
import Data.Set as Set (insert, minView, Set, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (hang, hcat, ptext, text, vcat)
import Language.Haskell.TH.Syntax (Lift(lift))
import Language.Haskell.TH.TypeGraph.Expand (E(E), unE)
import Language.Haskell.TH.TypeGraph.Prelude (unReify, unReifyName)
import Language.Haskell.TH.TypeGraph.Shape (Field)

-- | A vertex of the type graph.  Includes a type and (optionally)
-- what field of a parent type holds that type.  This allows special
-- treatment of a type depending on the type that contains it.
data TGV
    = TGV
      { _field :: Maybe Field -- ^ The record field which contains this type
      , _vsimple :: TGVSimple
      } deriving (Eq, Ord, Show, Data)

-- | For simple type graphs where no parent field information is required.
data TGVSimple
    = TGVSimple
      { _syns :: Set Name -- ^ All the type synonyms that expand to this type
      , _etype :: E Type -- ^ The fully expanded type
      } deriving (Eq, Ord, Show, Data)

tgv :: TGVSimple -> TGV
tgv v = TGV { _field = Nothing, _vsimple = v}

$(makeLenses ''TGV)
$(makeLenses ''TGVSimple)

instance Ppr TGVSimple where
    ppr (TGVSimple {_syns = ns, _etype = typ}) =
        hcat (ppr (unReify (view unE typ)) :
              case (Set.toList ns) of
                 [] -> []
                 _ ->   [ptext " ("] ++
                        intersperse (ptext ", ")
                          (List.concatMap (\ n -> [ptext ("aka " ++ show (unReifyName n))]) (Set.toList ns)) ++
                        [ptext ")"])

instance Ppr TGV where
    ppr (TGV {_field = fld, _vsimple = TGVSimple {_syns = ns, _etype = typ}}) =
        hcat (ppr (unReify (view unE typ)) :
              case (fld, Set.toList ns) of
                 (Nothing, []) -> []
                 _ ->   [ptext " ("] ++
                        intersperse (ptext ", ")
                          (List.concatMap (\ n -> [ptext ("aka " ++ show (unReifyName n))]) (Set.toList ns) ++
                           maybe [] (\ f -> [ppr f]) fld) ++
                        [ptext ")"])

instance Ppr ((), TGV, [TGV]) where
    ppr ((), v, vs) = vcat [hcat [ppr v, text ":"], hang (text "  ") 2 (vcat (map ppr vs))]

instance Ppr ((), TGVSimple, [TGVSimple]) where
    ppr ((), v, vs) = vcat [hcat [ppr v, text ":"], hang (text "  ") 2 (vcat (map ppr vs))]

instance Ppr (Map TGV (Set TGV)) where
    ppr mp = ppr (map (\(v, vs) -> ((), v, Set.toList vs)) (Map.toList mp))

instance Ppr (Map TGVSimple (Set TGVSimple)) where
    ppr mp = ppr (map (\(v, vs) -> ((), v, Set.toList vs)) (Map.toList mp))

instance Lift TGV where
    lift (TGV {_field = f, _vsimple = s}) = [|TGV {_field = $(lift f), _vsimple = $(lift s)}|]

instance Lift TGVSimple where
    lift (TGVSimple {_syns = ns, _etype = t}) = [|TGVSimple {_syns = $(lift ns), _etype = $(lift t)}|]

class TypeGraphVertex v where
    typeNames :: v -> Set Name
    -- ^ Return the set of 'Name' of a type's synonyms, plus the name (if
    -- any) used in its data declaration.  Note that this might return the
    -- empty set.
    bestType :: v -> Type

instance TypeGraphVertex TGV where
    typeNames = typeNames . _vsimple
    bestType = bestType . _vsimple

instance TypeGraphVertex TGVSimple where
    typeNames (TGVSimple {_etype = E (ConT tname), _syns = s}) = Set.insert tname s
    typeNames (TGVSimple {_syns = s}) = s
    bestType (TGVSimple {_etype = E (ConT name)}) = ConT name
    bestType v = maybe (let (E x) = view etype v in x) (ConT . fst) (Set.minView (view syns v))
