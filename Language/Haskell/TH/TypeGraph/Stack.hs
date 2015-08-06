-- | The HasStack monad used in MIMO to construct lenses that look
-- deep into a record type.  However, it does not involve the Path
-- type mechanism, and is unaware of View instances and other things
-- that modify the type graph.  Lets see how it adapts.
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.TH.TypeGraph.Stack
    ( StackElement(..)
    , prettyStack
    , foldField
      -- * Stack+instance map monad
    , HasStack
    , StackT
    , execStackT
    , withStack
    , push
      -- * Stack operations
    , stackAccessor
    , traceIndented
    , lensNamer
    ) where

import Control.Applicative
import Control.Category ((.))
import Control.Lens as Lens (iso, Lens', lens, set, view)
import Control.Monad.Readers (MonadReaders(ask, local), ReaderT, runReaderT)
import Data.Char (toUpper)
import Data.Generics (Data, Typeable)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.TypeGraph.Prelude (constructorName)
import Language.Haskell.TH.TypeGraph.Shape (FieldType(..), fName, fType, constructorFieldTypes)
import Prelude hiding ((.))

-- | The information required to extact a field value from a value.
-- We keep a stack of these as we traverse a declaration.  Generally,
-- we only need the field names.
data StackElement = StackElement FieldType Con Dec deriving (Eq, Show, Data, Typeable)

type HasStack = MonadReaders [StackElement]

withStack :: (Monad m, MonadReaders [StackElement] m) => ([StackElement] -> m a) -> m a
withStack f = ask >>= f

push :: MonadReaders [StackElement] m => FieldType -> Con -> Dec -> m a -> m a
push fld con dec = local (\stk -> StackElement fld con dec : stk)

traceIndented :: MonadReaders [StackElement] m => String -> m ()
traceIndented s = withStack $ \stk -> trace (replicate (length stk) ' ' ++ s) (return ())

prettyStack :: [StackElement] -> String
prettyStack = prettyStack' . reverse
    where
      prettyStack' :: [StackElement] -> String
      prettyStack' [] = "(empty)"
      prettyStack' (x : xs) = "[" ++ prettyElt x ++ prettyTail xs ++ "]"
      prettyTail [] = ""
      prettyTail (x : xs) = " → " ++ prettyElt x ++ prettyTail xs
      prettyElt (StackElement fld con dec) = prettyDec dec ++ ":" ++ prettyCon con ++ "." ++ pprint fld
      prettyDec (TySynD _ _ typ) = prettyType typ
      prettyDec (NewtypeD _ name _ _ _) = nameBase name
      prettyDec (DataD _ name _ _ _) = nameBase name
      prettyDec dec = error $ "prettyStack: " ++ show dec
      prettyCon = nameBase . constructorName
      prettyType (AppT t1 t2) = "((" ++ prettyType t1 ++ ") (" ++ prettyType t2 ++ "))"
      prettyType (ConT name) = nameBase name
      prettyType typ = "(" ++ show typ ++ ")"

-- | Push the stack and process the field.
foldField :: MonadReaders [StackElement] m => (FieldType -> m r) -> Dec -> Con -> FieldType -> m r
foldField doField dec con fld = push fld con dec $ doField fld

type StackT m = ReaderT [StackElement] m

execStackT :: Monad m => StackT m a -> m a
execStackT action = runReaderT action []

-- | Return a lambda function that turns a value of Type typ0 into the
-- type implied by the stack elements.
stackAccessor :: (Quasi m, MonadReaders [StackElement] m) => m Exp
stackAccessor =
    withStack f
    where
      f [] = runQ [|id|]
      f stk = do
        lns <- runQ $ stackLens stk
        Just typ <- stackType
        runQ [| \x -> (Lens.view $(pure lns) x) :: $(pure typ) |]

stackType :: MonadReaders [StackElement] m => m (Maybe Type)
stackType =
    withStack (return . f)
    where
      f [] = Nothing
      f (StackElement fld _ _ : _) = Just (fType fld)

-- | Return an expression of a lens for the value described by the
-- stack.
stackLens :: [StackElement] -> Q Exp
stackLens [] = [| iso id id |]
stackLens xs = mapM fieldLens xs >>= foldl1 (\ a b -> [|$b . $a|]) . map return

nthLens :: Int -> Lens' [a] a
nthLens n = lens (\ xs -> xs !! n) (\ xs x -> take (n - 1) xs ++ [x] ++ drop n xs)

-- | Generate a lens to access a field, as represented by the
-- StackElement type.
fieldLens :: StackElement -> Q Exp
fieldLens e@(StackElement fld con _) =
    do lns <-
           case fName fld of
              Right fieldName ->
                  -- Use the field name to build an accessor
                  let lensName = lensNamer (nameBase fieldName) in
                  lookupValueName lensName >>= maybe (error ("fieldLensName - missing lens: " ++ lensName)) varE
              Left fieldPos ->
                  -- Build a pattern expression to extract the field
                  do cname <- lookupValueName (nameBase $ constructorName con) >>= return . fromMaybe (error $ "fieldLens: " ++ show e)
                     f <- newName "f"
                     let n = length $ constructorFieldTypes con
                     as <- mapM newName (map (\ p -> "_a" ++ show p) [1..n])
                     [| lens -- \ (Con _ _ _ x _ _) -> x
                             $(lamE [conP cname (set (nthLens fieldPos) (varP f) (repeat wildP))] [| $(varE f) :: $(pure (fType fld)) |])
                             -- \ x (Con a b c _ d e) -> Con a b c x d e
                             $(lamE [conP cname (map varP as), varP f] (foldl appE (conE cname) (set (nthLens fieldPos) (varE f) (map varE as)))) |]
       [| $(pure lns) {- :: Lens $(pure top) $(pure (fType fld)) -} |]

-- | Given a field name, return the name to use for the corresponding lens.
lensNamer :: String -> String
lensNamer (n : ame) = "lens" ++ [toUpper n] ++ ame
lensNamer "" = error "Saw the empty string as a field name"
