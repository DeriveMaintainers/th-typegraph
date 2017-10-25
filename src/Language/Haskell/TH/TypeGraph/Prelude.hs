{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Language.Haskell.TH.TypeGraph.Prelude
    ( expandType, pprint1, pprint1', pprintW, pprintW'
    , ToName(toName)
    , HasMessageInfo(..), message, indent
    , composeType
    , decomposeType
    -- , unfoldType
    ) where

import Control.Lens (Lens', view)
import Control.Monad.RWS as Monad hiding (lift)
import Data.Generics (Data, everywhere, mkT)
import Instances.TH.Lift ()
import Language.Haskell.TH hiding (prim)
import Language.Haskell.TH.Desugar as DS (DsMonad, typeToTH, dsType, expand)
import Language.Haskell.TH.PprLib (to_HPJ_Doc)
import Language.Haskell.TH.Syntax as TH (Name(Name), NameFlavour(NameS), Quasi, VarStrictType)
import Language.Haskell.TH.TypeGraph.Orphans ()
import qualified Text.PrettyPrint as HPJ

-- | Pretty print a 'Ppr' value on a single line with each block of
-- white space (newlines, tabs, etc.) converted to a single space, and
-- all the module qualifiers removed from the names.  (If the data type
-- has no 'Name' values the friendlyNames function has no effect.)
pprint1 :: (Ppr a, Data a) => a -> [Char]
pprint1 = pprint1' . friendlyNames

pprint1' :: Ppr a => a -> [Char]
pprint1' = pprintStyle (HPJ.style {HPJ.mode = HPJ.OneLineMode})

-- | Pretty print with friendly names and wide lines
pprintW :: (Ppr a, Data a) => Int -> a -> [Char]
pprintW w = pprintW' w . friendlyNames

pprintW' :: Ppr a => Int -> a -> [Char]
pprintW' w = pprintStyle (HPJ.style {HPJ.lineLength = w})

-- | Helper function for pprint1 et. al.
pprintStyle :: Ppr a => HPJ.Style -> a -> String
pprintStyle style = HPJ.renderStyle style . to_HPJ_Doc . ppr

-- | Make a template haskell value more human reader friendly.  The
-- result almost certainly won't be compilable.  That's ok, though,
-- because the input is usually uncompilable - it imports hidden modules,
-- uses infix operators in invalid positions, puts module qualifiers in
-- places where they are not allowed, and maybe other things.
friendlyNames :: Data a => a -> a
friendlyNames =
    everywhere (mkT friendlyName)
    where
      friendlyName (Name x _) = Name x NameS -- Remove all module qualifiers

expandType :: DsMonad m  => Type -> m Type
expandType typ = DS.typeToTH <$> (DS.dsType typ >>= DS.expand)

-- | Copied from haskell-src-meta
class ToName a where toName :: a -> Name

instance ToName TyVarBndr where
  toName (PlainTV n) = n
  toName (KindedTV n _) = n

instance ToName Con where
    toName (ForallC _ _ con) = toName con
    toName (NormalC cname _) = cname
    toName (RecC cname _) = cname
    toName (InfixC _ cname _) = cname

instance ToName VarStrictType where
  toName (n, _, _) = n

class HasMessageInfo a where
    verbosity' :: Lens' a Int
    prefix' :: Lens' a String

-- | Output a verbosity controlled error message with the current
-- indentation.
message :: (Quasi m, MonadReader s m, HasMessageInfo s) =>
           Int -> String -> m ()
message minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ (runQ . runIO . putStr . indent p) s

-- | Indent the lines of a message.
indent :: String -> String -> String
indent p s = unlines $ fmap (p ++) (lines s)

decomposeType :: Type -> [Type]
decomposeType t0 = (go t0 [])
          where go (AppT t1 t2) ts = go t1 (t2 : ts)
                go t ts = t : ts

-- | Turn a type parameter list into type applications
composeType :: [Type] -> Type
composeType ts = foldl1 AppT ts

-- unfoldType :: Type -> (Type, [Type])
-- unfoldType t = go t []
--     where
--       go (AppT a p) ps = go a (p : ps)
--       go a ps = (a, ps)
