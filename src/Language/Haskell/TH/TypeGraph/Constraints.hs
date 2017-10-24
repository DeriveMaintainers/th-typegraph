-- | This module was developed to replace the deriveConstraints function in aeson,
-- but it probably could replace the code provided here for SafeCopy
-- and PathInfo.

{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, NamedFieldPuns,
    RankNTypes, UndecidableInstances #-}
{-# OPTIONS -Wall #-}

module Language.Haskell.TH.TypeGraph.Constraints
    ( deriveConstraints, monomorphize
    , withBindings, decompose, compose, toName
    ) where

import Control.Monad (MonadPlus, msum, when)
import Control.Monad.RWS (ask, execRWST, get, local, modify, MonadReader, tell, RWST)
import Control.Monad.Trans (lift)
import Data.Generics (Data, everywhere, mkT, listify, Typeable)
import Data.Map as Map (fromList, lookup, Map)
import Data.Set as Set (delete, empty, fromList, insert, member, Set, singleton)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Quasi)
import Language.Haskell.TH.TypeGraph.Prelude (pprint1, toName)

-- Reader monad type
data R =
    R { paramNames :: Set Name
      , verbosity :: Int
      , prefix :: String }

monomorphize :: TypeQ -> Q Type
monomorphize typq = typq >>= \typ0 -> go typ0 $ decompose typ0
    where
      go typ0 (ConT tname : vals) = reify tname >>= goInfo typ0 vals
      go typ0 _ = error $ "monomorphize - unexpected type " ++ pprint1 typ0
      goInfo _typ0 vals (TyConI dec) = goDec vals dec
      goInfo _typ0 vals (FamilyI dec _insts) = goDec vals dec
      goInfo typ0 _vals info = error $ "monomorphize - unexpected type " ++ pprint1 info ++ " (via " ++ pprint1 typ0 ++ ")"
#if MIN_VERSION_template_haskell(2,11,0)
      goDec vals (DataD _ tname vars _ _ _) = goVars (ConT tname) vals vars
      goDec vals (NewtypeD _ tname vars _ _ _) = goVars (ConT tname) vals vars
#else
      goDec vals (DataD _ tname vars _ _) = goVars (ConT tname) vals vars
      goDec vals (NewtypeD _ tname vars _ _) = goVars (ConT tname) vals vars
#endif
      -- These type variables are parameters to the data family type
      -- function, not to the type resulting from using the type
      -- function.  Therefore we do not bind them to the vals
      -- argument, they are unified with each instance.
      goDec vals (TySynD _tname vars typ) =
          withBindings vars vals (\unbound subst -> go (subst typ) (decompose typ ++ unbound))
#if MIN_VERSION_template_haskell(2,11,0)
      goDec vals (DataFamilyD fname fvars mkind) = do
#else
      goDec vals (FamilyD DataFam fname fvars mkind) = do
#endif
        -- We can learn the arity of this type from its kind.
        -- Then we can create extra type variables to make this
        -- monomorphic.
        let ftype = compose (ConT fname : map (VarT . toName) fvars)
        vars <- let kind = maybe [StarT] decompose mkind in
                mapM (\n -> newName ("t" ++ show n)) [1..(length kind - length fvars)]
        goVars ftype vals (fvars ++ map PlainTV vars)
      goDec vals dec = error $ "monomorphize - unexpected dec " ++ pprint1 dec ++ "(type params " ++ pprint1 (compose vals) ++ ")"
      goVars :: Type -> [Type] -> [TyVarBndr] -> Q Type
      goVars typ vals vars =
          if length vars < length vals
          then error $ "monomorphize - too many types applied to " ++ pprint1 typ ++ "\n  vars=" ++ show vars ++ "\n  vals=" ++ show vals
          else -- Extend the type list to match the var list by
               -- applying VarT to the extra variables.
               let vals' = vals ++ map (VarT . toName) (drop (length vals) vars) in
               -- Build the monomorphic type and apply substitutions
               withBindings vars vals (\unbound subst -> return (subst (compose (typ : vals'))))

deriveConstraints :: Int -> Name -> Name -> [Type] -> Q (Set Pred)
deriveConstraints verbosity0 constraint tyConName varTysExp = do
  typ <- monomorphize (pure (compose (ConT tyConName : varTysExp)))
  (_, preds) <-
     execRWST (go typ)
              (R { paramNames = Set.fromList (gFind varTysExp) :: Set Name
                 , verbosity = verbosity0
                 , prefix = "" })
              Set.empty
  return $ Set.delete (AppT (ConT constraint) (compose (ConT tyConName : varTysExp))) preds
    where
      go typ = do
        message 1 ("monomorphized: " ++ show typ)
        params <- paramNames <$> ask
        message 1 ("paramNames=" ++ show params)
        message 1 ("\nderiveConstraints " ++
                   pprint constraint ++
                   " (" ++ pprint (compose (ConT tyConName : varTysExp)) ++ ")")
        local (\r -> r {prefix = " " ++ prefix r}) $
          goType [] (compose (ConT tyConName : varTysExp))

      goType :: [Type] -> Type -> RWST R (Set Pred) (Set Type) Q ()
      goType vals typ = do
        visited <- get
        when (not (Set.member typ visited)) $ do
          modify (Set.insert typ)
          message 1 ("goType " ++ pprint typ)
          local (\r -> r {prefix = " " ++ prefix r}) $ do
            message 1 ("ts=" ++ show (decompose typ))
            goApply (decompose typ ++ vals)

      -- Process an unvisited type whose applications have been decomposed
      goApply :: [Type] -> RWST R (Set Pred) (Set Type) Q ()
      goApply [VarT name] = do
        message 1 ("goApply name=" ++ pprint name)
        -- params <- paramNames <$> ask
        -- Constraints are only interesting if they involve one of the
        -- type's parameters.
        let p = AppT (ConT constraint) (VarT name)
        tell (Set.singleton p)
{-
        when (Set.member name params)
          (do message 1 ("constraint: " ++ pprint p)
              tell (Set.singleton p))
-}
      -- Strip off kind signature (I should do something with this -
      -- it indicates whether the type is monomorphic.)
      goApply [SigT typ _kind] = goApply (decompose typ)
      -- goApplied [SigT _typ kind] = return ()
      goApply [ListT, val] = goType [] val
      goApply (TupleT _ : types) = mapM_ (goType []) types
      goApply (ConT tname : vals) = do
        info <- lift (reify tname)
        message 1 ("info=" ++ show info)
        goInfo vals info
      goApply (typ : _) = error ("goApplied - unexpected (unimplemented?) type: " ++ show typ ++ "\n typ0=" ++ pprint (compose (ConT tyConName : varTysExp)))
      goApply [] = error "Impossible value passed to goApplied"

      goInfo :: [Type] -> Info -> RWST R (Set Pred) (Set Type) Q ()
      goInfo vals (TyConI (TySynD _tname vars typ)) =
        withBindings vars vals (\unbound subst -> goType unbound (subst typ))
      goInfo _vals (PrimTyConI _ _ _) = return ()
      goInfo vals (TyConI dec) =
          let (vars, cons) = decInfo dec in
          withBindings vars vals (\unbound subst -> mapM_ (goCon unbound subst) cons)
      goInfo vals (FamilyI fam _insts) =
          let (famname, vars) = famInfo fam in
          withBindings vars vals
            (\unbound subst -> do
               let typ = subst (compose (ConT famname : fmap (VarT . toName) vars ++ unbound))
               params <- paramNames <$> ask
               message 1 ("paramNames=" ++ show params)
               message 1 ("typ=" ++ show typ)
               let p = AppT (ConT constraint) typ
               tell (Set.singleton p)
{-
                          if any (`Set.member` params) (gFind typ :: [Name])
                          then do
                            message 1 ("family constraint: " ++ pprint p)
                            tell (Set.singleton p)
                          else message 1 ("family constraint rejected: " ++ pprint1 p)
-}
            )
      goInfo _vals info = error ("deriveConstraints info=" ++ show info)

      decInfo :: Dec -> ([TyVarBndr], [Con])
#if MIN_VERSION_template_haskell(2,11,0)
      decInfo (DataD _cxt _tname vars _ cons _supers) = (vars, cons)
      decInfo (NewtypeD cx tname vars _ con supers) = (vars, [con])
#else
      decInfo (DataD _cxt _tname vars cons _supers) = (vars, cons)
      decInfo (NewtypeD _cx _tname vars con _supers) = (vars, [con])
#endif
      decInfo dec = error $ "unexpected Dec: " ++ pprint1 dec

#if MIN_VERSION_template_haskell(2,11,0)
      famInfo (DataFamilyD famname vars _mk) = (famname, vars)
#else
      famInfo (FamilyD DataFam famname vars _mk) = (famname, vars)
#endif
      famInfo fam = error $ "unexpected Dec: " ++ pprint1 fam

      goCon :: [Type] -> (Type -> Type) -> Con -> RWST R (Set Pred) (Set Type) Q ()
      goCon vals subst (ForallC _ _ con) =
          goCon vals subst con
      goCon vals subst (NormalC _cname sts) =
          mapM_ (goField vals subst . snd) sts
      goCon vals subst (RecC _cname vsts) =
          mapM_ (goField vals subst . (\(_,_,x) -> x)) vsts
      goCon vals subst (InfixC lhs _cname rhs) = do
          goField vals subst (snd lhs)
          goField vals subst (snd rhs)

      -- goField :: Data a => Name -> (a -> a) -> Int -> Int -> Name -> Type -> WriterT (Set Pred) Q ()
      goField vals subst ftype = goType vals (subst ftype)

-- | Input is a list of type variable bindings (such as those
-- appearing in a Dec) and the current stack of type parameters
-- applied by AppT.  Builds a function that expands a type using those
-- bindings and pass it to an action.
withBindings :: (Monad m, Data a) => [TyVarBndr] -> [Type] -> ([Type] -> (a -> a) -> m r) -> m r
withBindings vars vals action = do
  -- when (length vals < length vars)
  --   (error $ "doInfo - arity mismatch:\n\tvars=" ++ show vars ++
  --            "\n\tparams=" ++ show vals)
  let subst :: forall a. Data a => a -> a
      subst = substG bindings
      -- If there are more values than variables pass the extra
      -- unbound values to action.
      (vals', unbound) = splitAt (length vars) vals
      -- Make the type monomorphic by using the variable list to
      -- extend the list of values as necessary with self bindings.
      -- This prevents the arity mismatch error commented out above.
      vals'' = vals' ++ map (VarT . toName) (drop (length vals') vars)
      bindings = Map.fromList (zip (fmap toName vars) vals'')
  action unbound subst
    where
      -- Build a generic substitution function
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
