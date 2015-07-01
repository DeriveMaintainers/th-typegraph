-- | A fold on the shape of a record.
{-# LANGUAGE CPP, DeriveDataTypeable #-}
module Language.Haskell.TH.TypeGraph.Shape
    ( pprint'
    , unlifted
    -- * Deconstructors
    , constructorName
    , constructorFields
    , declarationName
    , declarationType
    -- * Field name and position
    , FieldType(..)
    , fPos
    , fName
    , fType
    -- * Decl shape
    , foldShape
    ) where

import Control.Applicative ((<$>), (<*>))
import Data.Generics (Data)
import Data.Typeable (Typeable)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax

instance Ppr () where
    ppr () = ptext "()"

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

-- FieldType and Field should be merged, or made less rudundant.

data FieldType = Positional Int StrictType | Named VarStrictType deriving (Eq, Ord, Show, Data, Typeable)

instance Ppr FieldType where
    ppr (Positional x _) = ptext $ show x
    ppr (Named (x, _, _)) = ptext $ nameBase x

fPos :: FieldType -> Either Int Name
fPos = fName

fName :: FieldType -> Either Int Name
fName (Positional x _) = Left x
fName (Named (x, _, _)) = Right x

fType :: FieldType -> Type
fType (Positional _ (_, x)) = x
fType (Named (_, _, x)) = x

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
constructorFields (NormalC _ ts) = map (uncurry Positional) (zip [1..] ts)
constructorFields (RecC _ ts) = map Named ts
constructorFields (InfixC t1 _ t2) = [Positional 1 t1, Positional 2 t2]

declarationName :: Monad m => Dec -> Maybe Name
declarationName (FunD name _) = Just name
declarationName (ValD _pat _body _decs) = Nothing
declarationName (DataD _ name _ _ _) = Just name
declarationName (NewtypeD _ name _ _ _) = Just name
declarationName (TySynD name _ _) = Just name
declarationName (ClassD _ name _ _ _) = Just name
declarationName (InstanceD _ _ _) = Nothing
declarationName (SigD name _) = Just name
declarationName (ForeignD _) = Nothing
declarationName (InfixD _ name) = Just name
declarationName (PragmaD _) = Nothing
declarationName (FamilyD _ _name _ _) = Nothing
declarationName (DataInstD _ name _ _ _) = Just name
declarationName (NewtypeInstD _ name _ _ _) = Just name
declarationName (TySynInstD name _) = Just name
declarationName (ClosedTypeFamilyD name _ _ _) = Just name
declarationName (RoleAnnotD name _) = Just name
#if MIN_VERSION_template_haskell(2,10,0)
declarationName (StandaloneDerivD _ _) = Nothing
declarationName (DefaultSigD name _) = Just name
#endif

declarationType :: Dec -> Maybe Type
declarationType = fmap ConT . declarationName
