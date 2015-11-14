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
    ( TypeStack(..)
    , topType
    , typeStack
    , StackElement(..)
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
import Control.Lens as Lens -- (iso, Lens', lens, set, view, (%=), (.~))
import Control.Monad.Reader (ask, ReaderT, runReaderT)
import Control.Monad.Readers (MonadReaders(askPoly, localPoly))
import Control.Monad.Trans (lift)
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
import Language.Haskell.TH.TypeGraph.TypeInfo (TypeInfo)
import Prelude hiding ((.))

-- | The information required to extact a field value from a value.
-- We keep a stack of these as we traverse a declaration.  Generally,
-- we only need the field names.
data StackElement = StackElement FieldType Con Dec deriving (Eq, Show, Data, Typeable)

-- | A stack describes a path from a top type down through fields of
-- its component types.
data TypeStack
    = TypeStack
      { _topType :: Type
      , _typeStack :: [StackElement]
      } deriving (Eq, Show, Data, Typeable)

$(makeLenses ''TypeStack)

type HasStack = MonadReaders TypeStack

withStack :: (Monad m, MonadReaders TypeStack m) => (TypeStack -> m a) -> m a
withStack f = askPoly >>= f

instance MonadReaders TypeInfo m => MonadReaders TypeInfo (ReaderT TypeStack m) where
    askPoly = lift askPoly
    localPoly f action = ask >>= runReaderT (localPoly f (lift action))

-- | push an element onto the TypeStack in m
push :: MonadReaders TypeStack m => FieldType -> Con -> Dec -> m a -> m a
push fld con dec action = localPoly (\(stk :: TypeStack) -> set typeStack (StackElement fld con dec : view typeStack stk) stk) action

traceIndented :: MonadReaders TypeStack m => String -> m ()
traceIndented s = withStack $ \stk -> trace (replicate (length (view typeStack stk)) ' ' ++ s) (return ())

prettyStack :: TypeStack -> String
prettyStack stk = prettyType (view topType stk) ++ " → " ++ prettyStack' (reverse (view typeStack stk))
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
foldField :: MonadReaders TypeStack m => (FieldType -> m r) -> Dec -> Con -> FieldType -> m r
foldField doField dec con fld = push fld con dec $ doField fld

type StackT m = ReaderT TypeStack m

execStackT :: Monad m => StackT m a -> Type -> m a
execStackT action type0 = runReaderT action (TypeStack {_topType = type0, _typeStack = []})

-- | Return a lambda function that turns a value of Type typ0 into the
-- type implied by the stack elements.
stackAccessor :: (Quasi m, MonadReaders TypeStack m) => m Exp
stackAccessor =
    withStack f
    where
      -- It works without this case, but this way the code is a little
      -- neater.  FIXME: Actually, we should have a stackView function
      -- that only builds the getter, we are just throwing away the
      -- lens's setter here.
      f stk | null (view typeStack stk) = runQ [|id|]
      f stk = do
        lns <- runQ $ stackLens stk
        Just typ <- stackType
        runQ [| \x -> (Lens.view $(pure lns) x) :: $(pure typ) |]

stackType :: MonadReaders TypeStack m => m (Maybe Type)
stackType =
    withStack (return . f . view typeStack)
    where
      f [] = Nothing
      f (StackElement fld _ _ : _) = Just (fType fld)

-- | Return an expression of a lens for the value described by the
-- stack.
stackLens :: TypeStack -> Q Exp
stackLens stk =
    case view typeStack stk of
      [] -> [| iso id id |]
      xs -> mapM fieldLens xs >>= foldl1 (\ a b -> [|$b . $a|]) . map return

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
