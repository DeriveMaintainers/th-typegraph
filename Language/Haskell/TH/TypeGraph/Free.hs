-- | Function to compute free type variable set for a Type.  (I took
-- this from somewhere, I really need to credit it.  Now when I search
-- all I can find is myself.)
{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TemplateHaskell #-}
module Language.Haskell.TH.TypeGraph.Free
    ( freeTypeVars
    ) where

import Control.Lens hiding (Strict, cons)
import Control.Monad.State (MonadState, execStateT)
import Data.Set as Set (Set, delete, difference, empty, fromList, insert, member)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.Syntax (Quasi(qReify))
import Language.Haskell.TH.TypeGraph.Prelude (pprint')

data St
    = St { _result :: Set Name
         , _visited :: Set Name
         } deriving Show

st0 :: St
st0 = St {_result = empty, _visited = empty}

$(makeLenses ''St)

-- | Return the names of the type variables that are free in x.  I.e.,
-- type variables that appear in the type expression but are not bound
-- by an enclosing forall or by the type parameters of a Dec.
freeTypeVars :: (FreeTypeVars t, Quasi m) => t -> m (Set Name)
freeTypeVars x = view result <$> execStateT (ftv x) st0

-- | This is based on the freeNamesOfTypes function from the
-- th-desugar package.
class FreeTypeVars t where
    ftv :: (Quasi m, MonadState St m) => t -> m ()

instance FreeTypeVars a => FreeTypeVars [a] where
    ftv ts = mapM_ ftv ts

instance FreeTypeVars Type where
    ftv (ForallT tvbs cx ty) = do
      ftv ty
      mapM_ go_pred cx
      result %= (`Set.difference` (Set.fromList (map tvbName tvbs)))
        where
#if __GLASGOW_HASKELL__ >= 709
          go_pred typ =
              -- This looks wrong as the one below looks wrong.  Wronger maybe.
              ftv typ
#else
          go_pred (ClassP _ tys) = ftv tys
          go_pred (EqualP t1 t2) = do
            -- This looks wrong - we need to unify t1 and t2 and look
            -- at the free type variables in the resulting bindings
            ftv t1
            ftv t2
#endif
    ftv (SigT ty _) = ftv ty
    ftv (VarT n) = result %= Set.insert n
    ftv (AppT t1 t2) = {-trace ("go_app " ++ show typ) (return ()) >>-} go_app [t2] t1
    ftv typ@(ConT _) = {-trace ("go_app " ++ show typ) (return ()) >>-} go_app [] typ
    ftv _ = return ()


go_app :: (Quasi m, MonadState St m) => [Type] -> Type -> m ()
go_app params (AppT t1 t2) = go_app (t2 : params) t1
go_app params (ConT n) = do
    stk <- use visited
    case Set.member n stk of
      True -> return ()
      False -> do
        visited %= Set.insert n
        qReify n >>= go_info (reverse params)
go_app params typ = mapM_ ftv (typ : params)
go_info :: (Quasi m, MonadState St m) => [Type] -> Info -> m ()
go_info params (TyConI dec) = go_dec params ({-trace ("go_dec " ++ show dec)-} dec)
go_info params (FamilyI dec _insts) = go_dec params dec
go_info _params (PrimTyConI _name _arity _unlifed) = return ()
go_info _params info = error $ "go_info - unexpected: " ++ pprint' info
go_dec :: (Quasi m, MonadState St m) => [Type] -> Dec -> m ()
go_dec params (NewtypeD cx tname tvs con supers) = go_dec params (DataD cx tname tvs [con] supers)
go_dec params (DataD _ tname tvs _ _) | length params > length tvs = error $ "Too many arguments to " ++ show tname
go_dec params (DataD _cx tname tvs cons _supers) = do
  -- For each type variable bound to a type parameter,
  -- replace the type variable with the free variables
  -- in the parameter
  ftv cons
  go_params tname tvs params
go_dec params (TySynD tname tvs typ) = do
  -- Add the free variables in the type, then subtract the ones that
  -- are bound here.
  ftv typ
  go_params tname tvs params

-- I have a feeling this is utterly wrong.  Example, with this class:
--
-- class OrderKey k => OrderMap k where
--    data Order k :: * -> *
--    ...
--
-- the resulting declaration of Order is
--
--    FamilyD DataFam Language.Haskell.TH.Path.Order.Order [PlainTV k,PlainTV $a] (Just StarT)
--    params=[ConT AbbrevPairID]
--
-- so the parameter is bound to k, and $a should be free.
go_dec params (FamilyD _flavour tname tvs _mkind) = go_params tname tvs params
go_dec params dec = error $ "go_dec - unexpected: " ++ pprint' dec ++ ", params=" ++ show params

go_params :: (Quasi m, MonadState St m) => Name -> [TyVarBndr] -> [Type] -> m ()
go_params tname tvs params | length params  > length tvs = error $ "Too many arguments to " ++ show tname
go_params _ tvs params = mapM_ (uncurry go_param) (zip tvs (map Just params ++ repeat Nothing))

-- | Update the free variable set for a type parameter
go_param :: (Quasi m, MonadState St m) => TyVarBndr -> Maybe Type -> m ()
go_param tvb (Just param) = do
  -- If there is a binding, add the free variables found in the type
  -- and remove the variable bound here
  -- trace ("go_param " ++ "(" ++ pprint tvb ++ ", " ++ pprint' param ++ ")") (return ())
  ftv param
  result %= Set.delete (tvbName tvb)
  -- let tv = tvbName tvb
  -- r <- use result
  -- when (Set.member tv r) (ftv param >> result %= Set.delete tv)
go_param tvb Nothing = do
  -- If there is a variable not bound to a type parameter it is fee
  result %= Set.insert (tvbName tvb)

{-
instance FreeTypeVars Info where
    ftv (TyConI dec) = ftv dec

instance FreeTypeVars Dec where
    ftv dec@(DataD _ _ _ _ _ _) = ftv dec
#if __GLASGOW_HASKELL__ >= 709
    go_pred = go
#else
    go_pred (ClassP _ tys) = freeNamesOfTypes tys
    go_pred (EqualP t1 t2) = go t1 <> go t2
#endif
-}

instance FreeTypeVars Con where
    ftv (NormalC _name sts) = ftv sts
    ftv (RecC _name vsts) = ftv vsts
    ftv (InfixC st1 _ st2) = ftv [st1, st2]
    -- I'm not sure what effect this forall has.
    ftv (ForallC _tvbs _cx con) = ftv con

instance FreeTypeVars (Strict, Type) where
    ftv (_, typ) = ftv typ

instance FreeTypeVars (Name, Strict, Type) where
    ftv (_, _, typ) = ftv typ

-- | Extract a 'Name' from a 'TyVarBndr'
tvbName :: TyVarBndr -> Name
tvbName (PlainTV n)    = n
tvbName (KindedTV n _) = n
