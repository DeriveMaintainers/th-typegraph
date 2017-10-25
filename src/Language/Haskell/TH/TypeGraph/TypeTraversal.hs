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
    ) where

import Control.Monad.RWS as Monad hiding (lift)
import Data.Generics (Data, everywhere, mkT)
import Data.List (intercalate)
import Data.Map.Strict as Map (Map, lookup)
import qualified Data.Map.Strict as Map (fromList)
import Instances.TH.Lift ()
import Language.Haskell.TH hiding (prim)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.TypeGraph.Orphans ()
import Language.Haskell.TH.TypeGraph.Prelude (expandType, pprint1, toName)

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
    doVarT :: Type -> Type -> m ()
    -- ^ Called when a type variable or type function is encountered.

doType :: HasTypeTraversal m => Type -> m ()
doType typ = doTypeOnce doTypeInternal typ

class DsMonad m => HasVisitedMap m where
    unvisited :: Type -> m () -> m () -- ^ Perform action if type has not been visted

doTypeOnce :: HasVisitedMap m => (Type -> m ()) -> Type -> m ()
doTypeOnce go typ = unvisited typ (go typ)

doApply :: (HasTypeTraversal m, HasTypeParameters m, DsMonad m) => Type -> Type -> m ()
doApply typ0 (ForallT _tvs _cxt typ) = doApply typ0 typ
doApply typ0 (VarT name) = doVarT typ0 (VarT name)
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
doInfo typ0 (TyConI dec) =
    let (tname, binds, cons) = decInfo dec in
    withBindings (\subst -> do mapM_ (uncurry (doCon typ0 tname subst (length cons))) (zip [1..] cons)) binds
-- Encountered a declaration like data family (ProxyType t).  Call
-- doVarT on the assumption that ProxyType t is a concrete type.  I'm
-- not sure if this is the best possible implementation, but its
-- better than what we have now.
doInfo typ0 (FamilyI dec _insts) =
  let (tname, binds) = famInfo dec in
  withBindings (\subst -> doVarT typ0 (subst (foldl AppT (ConT tname) (fmap (VarT . toName) binds)))) binds
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
doCon typ0 tname subst cct cpos (NormalC cname sts) =
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

decInfo :: Dec -> (Name, [TyVarBndr], [Con])
#if MIN_VERSION_template_haskell(2,11,0)
decInfo (NewtypeD _ tname binds _mk con _supers) = (tname, binds, [con])
decInfo (DataD _ tname binds _mk cons _supers) = (tname, binds, cons)
#else
decInfo (NewtypeD _cx tname binds con _supers) = (tname, binds, [con])
decInfo (DataD _ tname binds cons _supers) = (tname, binds, cons)
#endif
decInfo _ = error "decInfo"

famInfo :: Dec -> (Name, [TyVarBndr])
#if MIN_VERSION_template_haskell(2,11,0)
famInfo (DataFamilyD typ binds _mk) = (typ, binds)
#else
famInfo (FamilyD DataFam typ binds _mk) = (typ, binds)
#endif
famInfo _ = error "famInfo"
