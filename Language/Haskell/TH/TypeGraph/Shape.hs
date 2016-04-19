-- | A fold on the shape of the constructors of a DataD or NewtypeD record.
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Haskell.TH.TypeGraph.Shape
    ( 
    -- * Field name and position
      Field
    , FieldType(..)
    , fieldType
    , constructorName
    , constructorFields
    , constructorFieldTypes
    , constructorPat
    , fPos
    , fName
    , fType
    -- * Decl shape
    , foldShape
    ) where

import Data.Generics (Data)
import Data.Typeable (Typeable)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.TypeGraph.Prelude (unReifyName)
import Language.Haskell.TH.TypeGraph.Expand (E)

-- FieldType and Field should be merged, or made less rudundant.

type Field = ( Name, -- type name
               Con,  -- constructor
               Either Int -- field position
                      Name -- field name
             )

instance Ppr Field where
    ppr (tname, con, field) = ptext $
        "field " ++
        show (unReifyName tname) ++ "." ++
        either (\ n -> show (unReifyName (constructorName con)) ++ "[" ++ show n ++ "]") (\ f -> show (unReifyName f)) field

instance Ppr (Maybe Field, E Type) where
    ppr (mf, typ) = ptext $ pprint typ ++ maybe "" (\fld -> " (field " ++ pprint fld ++ ")") mf

instance Ppr (Maybe Field, Type) where
    ppr (mf, typ) = ptext $ pprint typ ++ " (unexpanded)" ++ maybe "" (\fld -> " (field " ++ pprint fld ++ ")") mf

data FieldType = Positional Int StrictType | Named VarStrictType deriving (Eq, Ord, Show, Data, Typeable)

fieldType :: FieldType -> Type
fieldType (Positional _ (_, ftype)) = ftype
fieldType (Named (_, _, ftype)) = ftype

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
    case zip cons (map constructorFieldTypes cons) :: [(Con, [FieldType])] of
      [(con, [fld])] ->
          wrapperFn con fld
      [(con, flds)] ->
          recordFn con flds
      pairs | all (== 0) (map (length . snd) pairs) ->
          enumFn (map fst pairs)
      pairs ->
          dataFn pairs

constructorFieldTypes :: Con -> [FieldType]
constructorFieldTypes (ForallC _ _ con) = constructorFieldTypes con
constructorFieldTypes (NormalC _ ts) = map (uncurry Positional) (zip [1..] ts)
constructorFieldTypes (RecC _ ts) = map Named ts
constructorFieldTypes (InfixC t1 _ t2) = [Positional 1 t1, Positional 2 t2]

constructorFields :: Name -> Con -> [Field]
constructorFields tname (ForallC _ _ con) = constructorFields tname con
constructorFields tname con@(NormalC _cname fields) = map (\(i, _) -> (tname, con, Left i)) (zip ([1..] :: [Int]) fields)
constructorFields tname con@(RecC _cname fields) = map (\ (fname, _, _typ) -> (tname, con, Right fname)) fields
constructorFields tname con@(InfixC (_, _lhs) _cname (_, _rhs)) = [(tname, con, Left 1), (tname, con, Left 2)]

constructorName :: Con -> Name
constructorName (ForallC _ _ con) = constructorName con
constructorName (NormalC cname _) = cname
constructorName (RecC cname _) = cname
constructorName (InfixC _ cname _) = cname

-- | Build a pattern that will match only values with the given constructor.
constructorPat :: Con -> PatQ
constructorPat (ForallC _ _ con) = constructorPat con
constructorPat (NormalC cname _) = recP cname []
constructorPat (RecC cname _) = recP cname []
constructorPat (InfixC _ cname _) = infixP wildP cname wildP
