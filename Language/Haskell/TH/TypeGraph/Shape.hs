-- | A fold on the shape of a record.
{-# LANGUAGE DeriveDataTypeable #-}
module Language.Haskell.TH.TypeGraph.Shape
    ( FieldType(..)
    , fPos
    , fName
    , fType
    , foldShape
    -- * Constructor deconstructors
    , constructorName
    , constructorFields
    ) where

import Data.Generics (Data)
import Data.Typeable (Typeable)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax

-- FieldType and Field should be merged, or made less rudundant.

data FieldType = Positional Int StrictType | Named VarStrictType deriving (Eq, Ord, Show, Data, Typeable)

instance Ppr FieldType where
    ppr (Positional x _) = ptext $ show x
    ppr (Named (x, _, _)) = ptext $ nameBase x

fPos :: FieldType -> Maybe Int
fPos (Positional x _) = Just x
fPos (Named _) = Nothing

fName :: FieldType -> Maybe Name
fName (Positional _ _) = Nothing
fName (Named (x, _, _)) = Just x

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
