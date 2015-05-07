-- | Helper functions for dealing with record fields, type shape, type
-- arity, primitive types, and pretty printing.
{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleInstances, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Haskell.TH.TypeGraph.Core
    ( -- * Declaration shape
      FieldType(FieldType, fPos, fNameAndType)
    , fName
    , fType
    , prettyField
    , constructorFields
    , foldShape
    -- * Constructor deconstructors
    , constructorName
    -- * Queries
    , typeArity
    , unlifted
    -- * Pretty print without extra whitespace
    , pprint'
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>), (<*>))
#endif
import Data.Data (Data)
import Data.Map as Map (Map, fromList, toList)
import Data.Set as Set (Set, fromList, toList)
import Data.Typeable (Typeable)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.TypeGraph.Expand (E, markExpanded, runExpanded)

data FieldType
    = FieldType
      { fPos :: Int
      , fNameAndType :: Either StrictType VarStrictType }
    deriving (Eq, Ord, Show, Data, Typeable)

fName :: FieldType -> Maybe Name
fName = either (\ (_, _) -> Nothing) (\ (x, _, _) -> Just x) . fNameAndType

prettyField :: FieldType -> String
prettyField fld = maybe (show (fPos fld)) nameBase (fName fld)

-- | fType' with leading foralls stripped
fType :: FieldType -> Type
fType = either (\ (_, x) -> x) (\ (_, _, x) -> x) . fNameAndType

-- | Given the list of constructors from a Dec, dispatch on the
-- different levels of complexity of the type they represent - a
-- wrapper is a single arity one constructor, an enum is
-- several arity zero constructors, and so on.
foldShape :: Monad m =>
             ([(Con, [FieldType])] -> m r) -- dataFn - several constructors not all of which are arity zero
          -> (Con -> [FieldType] -> m r)   -- recordFn - one constructor which has arity greater than one
          -> ([Con] -> m r)                -- enumFn - all constructors are of arity zero
          -> (Con -> FieldType -> m r)     -- wrapperFn - one constructor of arity one
          -> [Con] -> m r
foldShape dataFn recordFn enumFn wrapperFn cons =
    case zip cons (map constructorFields cons) :: [(Con, [FieldType])] of
      [(con, [fld])] ->
          wrapperFn con fld
      [(con, flds)] ->
          recordFn con flds
      pairs | all (== 0) (map (length . snd) pairs) ->
          enumFn (map fst pairs)
      pairs ->
          dataFn pairs

constructorName :: Con -> Name
constructorName (ForallC _ _ con) = constructorName con
constructorName (NormalC name _) = name
constructorName (RecC name _) = name
constructorName (InfixC _ name _) = name

constructorFields :: Con -> [FieldType]
constructorFields (ForallC _ _ con) = constructorFields con
constructorFields (NormalC _ ts) = map (uncurry FieldType) (zip [1..] (map Left ts))
constructorFields (RecC _ ts) = map (uncurry FieldType) (zip [1..] (map Right ts))
constructorFields (InfixC t1 _ t2) = map (uncurry FieldType) [(1, Left t1), (2, Left t2)]

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

instance Lift a => Lift (Set a) where
    lift s = [|Set.fromList $(lift (Set.toList s))|]

instance (Lift a, Lift b) => Lift (Map a b) where
    lift mp = [|Map.fromList $(lift (Map.toList mp))|]

instance Lift (E Type) where
    lift etype = [|markExpanded $(lift (runExpanded etype))|]
