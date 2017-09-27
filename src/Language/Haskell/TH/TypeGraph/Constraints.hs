-- | This module was developed to replace the deriveConstraints function in aeson,
-- but it probably could replace the code provided here for SafeCopy
-- and PathInfo.

{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, NamedFieldPuns,
    RankNTypes, UndecidableInstances #-}
{-# OPTIONS -Wall #-}

module Language.Haskell.TH.TypeGraph.Constraints
    ( deriveConstraints
    ) where

import Control.Monad (MonadPlus, msum, when)
import Control.Monad.RWS (ask, execRWST, get, local, modify, MonadReader, tell, RWST)
import Control.Monad.Trans (lift)
import Data.Generics (Data, everywhere, mkT, listify, Typeable)
import Data.Map as Map (fromList, lookup, Map)
import Data.Set as Set (empty, fromList, insert, member, Set, singleton)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Quasi)
import Language.Haskell.TH.TypeGraph.TypeTraversal (toName)

-- Reader monad type
data R =
    R { paramNames :: Set Name
      , verbosity :: Int
      , prefix :: String }

deriveConstraints :: Int -> Name -> Name -> [Type] -> Q (Set Pred)
deriveConstraints verbosity0 constraint tyConName varTysExp = do
  snd <$> execRWST
            (do message 1 ("deriveConstraints " ++ pprint constraint ++ " (" ++ pprint (compose (ConT tyConName : varTysExp)))
                local (\r -> r {prefix = " " ++ prefix r}) $
                  goType (compose (ConT tyConName : varTysExp)))
            -- Find all the type variables in the original type.
            -- Constraints are only necessary if they involve one or
            -- more of these.
            (R { paramNames = Set.fromList (gFind varTysExp) :: Set Name
               , verbosity = verbosity0
               , prefix = "" })
            Set.empty
    where
      goType :: Type -> RWST R (Set Pred) (Set Type) Q ()
      -- Constraints are only interesting if they involve one of the
      -- types parameters.
      goType typ@(VarT name) = do
        params <- paramNames <$> ask
        when (Set.member name params)
          (do let p = AppT (ConT constraint) typ
              message 1 ("constraint: " ++ pprint p)
              tell (Set.singleton p))
      goType (SigT typ _kind) = goType typ
      goType typ = do
        visited <- get
        when (not (Set.member typ visited)) $ do
          modify (Set.insert typ)
          message 1 ("goType " ++ pprint typ)
          local (\r -> r {prefix = " " ++ prefix r}) $ goApplied (decompose typ)

      goApplied :: [Type] -> RWST R (Set Pred) (Set Type) Q ()
      -- goApplied [SigT _typ kind] = return ()
      goApplied [ListT, val] = goType val
      goApplied (TupleT _ : types) = mapM_ goType types
      goApplied (ConT tname : vals) =
        lift (reify tname) >>= goInfo vals
      goApplied (typ : _) = error ("goApplied - unexpected (unimplemented?) type: " ++ show typ ++ "\n typ0=" ++ pprint (compose (ConT tyConName : varTysExp)))
      goApplied [] = error "Impossible value passed to goApplied"

      goInfo :: [Type] -> Info -> RWST R (Set Pred) (Set Type) Q ()
      goInfo vals (TyConI (TySynD _tname vars typ)) =
          withBindings vals vars (\subst -> goType (subst typ))
      goInfo vals (TyConI (DataD _cxt _tname vars cons _supers)) =
          withBindings vals vars (\subst -> mapM_ (goCon subst) cons)
      goInfo vals (TyConI (NewtypeD cx tname vars con supers)) =
          goInfo vals (TyConI (DataD cx tname vars [con] supers))
      goInfo _vals (PrimTyConI _ _ _) = return ()
      goInfo vals (FamilyI (FamilyD DataFam famname vars _mk) _insts) = do
        withBindings vals vars (\subst -> do let typ = subst (compose (ConT famname : fmap (VarT . toName) vars))
                                             params <- paramNames <$> ask
                                             when (any (`Set.member` params) (gFind typ :: [Name]))
                                                  (tell (Set.singleton (AppT (ConT constraint) typ))))
      goInfo _vals info = error ("deriveConstraints info=" ++ show info)

      -- goCon :: Data a => Name -> (a -> a) -> Int -> Int -> Con -> WriterT (Set Pred) Q ()
      goCon subst (ForallC _ _ con) =
          goCon subst con
      goCon subst (NormalC _cname sts) =
          mapM_ (goField subst . snd) sts
      goCon subst (RecC _cname vsts) =
          mapM_ (goField subst . (\(_,_,x) -> x)) vsts
      goCon subst (InfixC lhs _cname rhs) = do
          goField subst (snd lhs)
          goField subst (snd rhs)

      -- goField :: Data a => Name -> (a -> a) -> Int -> Int -> Name -> Type -> WriterT (Set Pred) Q ()
      goField subst ftype = goType (subst ftype)

-- | Input is a list of type variable bindings (such as those
-- appearing in a Dec) and the current stack of type parameters
-- applied by AppT.  Builds a function that expands a type using those
-- bindings and pass it to an action.
withBindings :: (Monad m, Data a) => [Type] -> [TyVarBndr] -> ((a -> a) -> m ()) -> m ()
withBindings vals vars action = do
  when (length vals < length vars)
    (error $ "doInfo - arity mismatch:\n\tvars=" ++ show vars ++
             "\n\tparams=" ++ show vals)
  let subst :: forall a. Data a => a -> a
      subst = substG bindings
      bindings = Map.fromList (zip (fmap toName vars) (vals :: [Type]))
  action subst
    where
      substG :: forall a. Data a => Map Name Type -> a -> a
      substG bindings typ = everywhere (mkT (subst1 bindings)) typ

      subst1 :: Map Name Type -> Type -> Type
      subst1 bindings t@(VarT name) = maybe t id (Map.lookup name bindings)
      subst1 _ t = t

gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)

decompose :: Type -> [Type]
decompose t0 = go t0 []
    where go (AppT t1 t2) ts = go t1 (t2 : ts)
          go t ts = t : ts

compose :: [Type] -> Type
compose types = foldl1 AppT types

-- | Output a verbosity controlled error message with the current
-- indentation.
message :: (Quasi m, MonadReader R m) =>
           Int -> String -> m ()
message minv s = do
    v <- verbosity <$> ask
    p <- prefix <$> ask
    when (v >= minv) $ (runQ . runIO . putStr . indent p) s

-- | Indent the lines of a message.
indent :: String -> String -> String
indent p s = unlines $ fmap (p ++) (lines s)
