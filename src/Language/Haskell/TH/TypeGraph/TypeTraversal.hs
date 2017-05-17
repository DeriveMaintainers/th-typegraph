-- | Build a directed graph whose nodes are arity zero types and whose
-- edges represent the hops in the path graph.

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Language.Haskell.TH.TypeGraph.TypeTraversal
    ( HasVisitedMap(..)
    , doType
    , HasTypeParameters(..)
    , withBindings
    , HasTypeTraversal(..)
    , doApply
    , FieldInfo(..)
    , expandType, pprint1, pprint1', pprintW, pprintW'
    , ToName(toName)
    , HasMessageInfo(..), message, indent
    ) where

import Control.Lens (Lens', view)
import Control.Monad.RWS as Monad hiding (lift)
import Data.Generics (Data, everywhere, mkT)
import Data.List (intercalate)
import Data.Map.Strict as Map (Map, lookup)
import qualified Data.Map.Strict as Map (fromList)
-- import Debug.Trace
import Instances.TH.Lift ()
import Language.Haskell.TH hiding (prim)
import Language.Haskell.TH.Desugar as DS (DsMonad, typeToTH, dsType, expand)
import Language.Haskell.TH.PprLib (to_HPJ_Doc)
import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.TypeGraph.Orphans ()
import qualified Text.PrettyPrint as HPJ

class Monad m => HasTypeParameters m where
    pushParam :: Type -> m a -> m a -- ^ Push a parameter
    withParams :: ([Type] -> m ()) -> m ()

data FieldInfo
    = FieldInfo
      { _typeName :: Name
      , _constrCount :: Int
      , _constrIndex :: Int
      , _constrName :: Name
      , _fieldCount :: Int
      , _fieldIndex :: Int
      , _fieldName :: Maybe Name
      , _fieldType :: Type
      } deriving Show

class (DsMonad m, HasVisitedMap m) => HasTypeTraversal m where
    prepType :: Type -> m Type
    -- ^ Normally just 'return', this can modify the types during the
    -- traversal.
    doTypeInternal :: Type -> m ()
    -- ^ This is passed every type that is encountered.  The methods
    -- below are called from doApply.
    doListT :: Type -> Type -> m ()
    -- ^ When a ListT type is encountered this is passed the type and
    -- the element type
    doTupleT :: Type -> Type -> Int -> m ()
    -- ^ When a TupleT type is encountered this is called once for
    -- each element, with the type, element type, and element
    -- position.
    doField :: Type -> (Type -> Type) -> FieldInfo -> m ()
    -- ^ When a field is encountered this is called with all the
    -- field info - type name, constructor count/position/name,
    -- field count/position/type/maybe name.
    doVarT :: Type -> Name -> m ()
    -- ^ Called when a type variable is encountered.

doType :: HasTypeTraversal m => Type -> m ()
doType typ = prepType typ >>= doTypeOnce doTypeInternal

class DsMonad m => HasVisitedMap m where
    unvisited :: Type -> m () -> m () -- ^ Perform action if type has not been visted

doTypeOnce :: HasVisitedMap m => (Type -> m ()) -> Type -> m ()
doTypeOnce go typ = unvisited typ (go typ)

doApply :: (HasTypeTraversal m, HasTypeParameters m, DsMonad m) => Type -> Type -> m ()
doApply typ0 (ForallT tvs cxt typ) = doApply typ0 typ
doApply typ0 (VarT name) = doVarT typ0 name
doApply typ0 (AppT a b) = pushParam b (doApply typ0 a)
doApply typ0 (ConT tname) = qReify tname >>= doInfo typ0
doApply typ0 ListT = do
  withParams $ \ps -> do
    case ps of
      [a] -> doListT typ0 a
      _ -> error $ "ListT Arity error: "
doApply typ0 typ@(TupleT n) = do
  withParams $ \ps -> do
    when (length ps /= n) (error $ "Tuple Arity error: " ++
                                   pprint1 typ ++
                                   " [" ++ intercalate ", " (fmap pprint1 ps) ++ "]")
    mapM_ (uncurry (doTupleT typ0)) (zip ps [1..])
doApply typ0 _ = do
  error $ "doApply - unexpected type: " ++ pprint1 typ0

doInfo :: (DsMonad m, HasTypeParameters m, HasTypeTraversal m) => Type -> Info -> m ()
doInfo _typ0 (PrimTyConI _name _arity _unl) = pure ()
doInfo _typ0 (TyConI (TySynD _tname binds typ)) =
    runQ (expandType typ) >>= \typ' ->
    withBindings (\subst -> doType (subst typ')) binds
#if MIN_VERSION_template_haskell(2,11,0)
doInfo typ0 (TyConI (NewtypeD cx tname binds mk con supers)) =
    doInfo typ0 (TyConI (DataD cx tname binds mk [con] supers))
doInfo typ0 (TyConI (DataD _ tname binds _mk cons _supers)) =
    withBindings (\subst -> do mapM_ (uncurry (doCon typ0 tname subst (length cons))) (zip [1..] cons)) binds
#else
doInfo typ0 (TyConI (NewtypeD cx tname binds con supers)) =
    doInfo typ0 (TyConI (DataD cx tname binds [con] supers))
doInfo typ0 (TyConI (DataD _ tname binds cons _supers)) =
    withBindings (\subst -> do mapM_ (uncurry (doCon typ0 tname subst (length cons))) (zip [1..] cons)) binds
#endif
doInfo _ info = error $ "Unexpected info: " ++ pprint1 info ++ "\n\t" ++ show info

doCon :: (HasTypeParameters m, HasTypeTraversal m) => Type -> Name -> (Type -> Type) -> Int -> Int -> Con -> m ()
doCon typ0 tname subst cct cpos (ForallC _ _ con) = doCon typ0 tname subst cct cpos con
doCon typ0 tname subst cct cpos (RecC cname vsts) =
  mapM_ (\(i, (fname, _, ftype)) ->
             expandType ftype >>= \ftype' ->
             let fld = FieldInfo { _typeName = tname
                                 , _constrCount = cct
                                 , _constrIndex = cpos
                                 , _constrName = cname
                                 , _fieldCount = length vsts
                                 , _fieldIndex = i
                                 , _fieldName = Just fname
                                 , _fieldType = subst ftype' } in
             doField typ0 subst fld) (zip [1..] vsts)
doCon typ0 tname subst cct cpos con@(NormalC cname sts) =
  mapM_ (\(i, (_, ftype)) ->
             expandType ftype >>= \ftype' ->
             let fld = FieldInfo { _typeName = tname
                                 , _constrCount = cct
                                 , _constrIndex = cpos
                                 , _constrName = cname
                                 , _fieldCount = length sts
                                 , _fieldIndex = i
                                 , _fieldName = Nothing
                                 , _fieldType = subst ftype' } in
             doField typ0 subst fld) (zip [1..] sts)
doCon typ0 tname subst cct cpos (InfixC lhs cname rhs) =
  mapM_ (\(i, (_, ftype)) ->
             expandType ftype >>= \ftype' ->
             let  fld = FieldInfo { _typeName = tname
                                  , _constrCount = cct
                                  , _constrIndex = cpos
                                  , _constrName = cname
                                  , _fieldCount = 2
                                  , _fieldIndex = i
                                  , _fieldName = Nothing
                                  , _fieldType = subst ftype' } in
             doField typ0 subst fld) [(1, lhs), (2, rhs)]

-- | Input is a list of type variable bindings (such as those
-- appearing in a Dec) and the current stack of type parameters
-- applied by AppT.  Builds a function that expands a type using those
-- bindings and pass it to an action.
withBindings :: (HasTypeParameters m, Data a) => ((a -> a) -> m ()) -> [TyVarBndr] -> m ()
withBindings action vars = do
  withParams $ \vals -> do
    when (length vals < length vars)
      (error $ "doInfo - arity mismatch:\n\tvars=" ++ show vars ++
               "\n\tparams=" ++ show vals)
    let subst :: forall a. Data a => a -> a
        subst = substG bindings
        bindings = Map.fromList (zip (fmap toName vars) ({-fmap subst-} vals :: [Type]))
    action subst
    where
      substG :: forall a. Data a => Map Name Type -> a -> a
      substG bindings typ = everywhere (mkT (subst1 bindings)) typ

      subst1 :: Map Name Type -> Type -> Type
      subst1 bindings t@(VarT name) = maybe t id (Map.lookup name bindings)
      subst1 _ t = t

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
