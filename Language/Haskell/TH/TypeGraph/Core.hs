-- | Helper functions for dealing with record fields, type arity,
-- primitive types, and pretty printing.
{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleInstances, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Haskell.TH.TypeGraph.Core
    ( -- * Type describing a record field
      Field
    -- * Queries
    , typeArity
    , unlifted
    -- * Pretty print without extra whitespace
    , pprint'
    , unReify
    , unReifyName
    ) where

import Control.Applicative ((<$>), (<*>))
import Data.Generics (Data, everywhere, mkT)
import Data.Map as Map (Map, fromList, toList)
import Data.Set as Set (Set, fromList, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.TypeGraph.Expand (E, markExpanded, runExpanded)

type Field = ( Name, -- type name
               Name, -- constructor name
               Either Int -- field position
                      Name -- field name
             )

instance Ppr () where
    ppr () = ptext "()"

instance Ppr Field where
    ppr (tname, cname, field) = ptext $
        "field " ++
        show (unReifyName tname) ++ "." ++
        either (\ n -> show (unReifyName cname) ++ "[" ++ show n ++ "]") (\ f -> show (unReifyName f)) field

instance Ppr (Maybe Field, E Type) where
    ppr (mf, typ) = ptext $ pprint typ ++ maybe "" (\fld -> " (field " ++ pprint fld ++ ")") mf

instance Ppr (Maybe Field, Type) where
    ppr (mf, typ) = ptext $ pprint typ ++ " (unexpanded)" ++ maybe "" (\fld -> " (field " ++ pprint fld ++ ")") mf

-- | Compute the arity of a type - the number of type parameters that
-- must be applied to it in order to obtain a concrete type.
typeArity :: Quasi m => Type -> m Int
typeArity (ForallT _ _ typ) = typeArity typ
typeArity ListT = return 1
typeArity (VarT _) = return 1
typeArity (TupleT n) = return n
typeArity (AppT t _) = typeArity t >>= \ n -> return $ n - 1
typeArity (ConT name) = qReify name >>= infoArity
    where
      infoArity (TyConI dec) = decArity dec
      infoArity (PrimTyConI _ _ _) = return 0
      infoArity (FamilyI dec _) = decArity dec
      infoArity info = error $ "typeArity - unexpected: " ++ pprint' info
      decArity (DataD _ _ vs _ _) = return $ length vs
      decArity (NewtypeD _ _ vs _ _) = return $ length vs
      decArity (TySynD _ vs t) = typeArity t >>= \ n -> return $ n + length vs
      decArity (FamilyD _ _ vs _mk) = return $ {- not sure what to do with the kind mk here -} length vs
      decArity dec = error $ "decArity - unexpected: " ++ show dec
typeArity typ = error $ "typeArity - unexpected type: " ++ show typ

-- | Pretty print a 'Ppr' value on a single line with each block of
-- white space (newlines, tabs, etc.) converted to a single space.
pprint' :: Ppr a => a -> [Char]
pprint' typ = unwords $ words $ pprint typ

unReify :: Data a => a -> a
unReify = everywhere (mkT unReifyName)

unReifyName :: Name -> Name
unReifyName = mkName . nameBase

instance Lift a => Lift (Set a) where
    lift s = [|Set.fromList $(lift (Set.toList s))|]

instance (Lift a, Lift b) => Lift (Map a b) where
    lift mp = [|Map.fromList $(lift (Map.toList mp))|]

instance Lift (E Type) where
    lift etype = [|markExpanded $(lift (runExpanded etype))|]

-- | Does the type or the declaration to which it refers contain a
-- primitive (aka unlifted) type?  This will traverse down any 'Dec'
-- to the named types, and then check whether any of their 'Info'
-- records are 'PrimTyConI' values.
class IsUnlifted t where
    unlifted :: Quasi m => t -> m Bool

instance IsUnlifted Dec where
    unlifted (DataD _ _ _ cons _) = or <$> mapM unlifted cons
    unlifted (NewtypeD _ _ _ con _) = unlifted con
    unlifted (TySynD _ _ typ) = unlifted typ
    unlifted _ = return False

instance IsUnlifted Con where
    unlifted (ForallC _ _ con) = unlifted con
    unlifted (NormalC _ ts) = or <$> mapM (unlifted . snd) ts
    unlifted (RecC _ ts) = or <$> mapM (\ (_, _, t) -> unlifted t) ts
    unlifted (InfixC t1 _ t2) = or <$> mapM (unlifted . snd) [t1, t2]

instance IsUnlifted Type where
    unlifted (ForallT _ _ typ) = unlifted typ
    unlifted (ConT name) = qReify name >>= unlifted
    unlifted (AppT t1 t2) = (||) <$> unlifted t1 <*> unlifted t2
    unlifted _ = return False

instance IsUnlifted Info where
    unlifted (PrimTyConI _ _ _) = return True
    unlifted _ = return False -- traversal stops here
