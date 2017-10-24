-- | Compute which type parameters are phantom types.

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Language.Haskell.TH.TypeGraph.Phantom
    ( nonPhantom
    ) where

import Control.Lens ((%=), _1, makeLenses, over, use, view)
import Control.Monad.RWS hiding (lift)
import Language.Haskell.TH.TypeGraph.Prelude (expandType, HasMessageInfo(..), message, pprint1, toName)
import Language.Haskell.TH.TypeGraph.TypeTraversal
import Data.Set as Set
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)

-- | The reader monad type used while generating a 'TypeGraph'.
data R
    = R
      { _params :: [Type]
      -- ^ Positional type parameters.  When @AppT a b@ is
      -- encountered, @b@ is pushed onto the stack and @a@ is
      -- processed.  Then when a type name is reified and is
      -- found to have type variables, they are bound to the
      -- type parameters which are on the stack.
      , _verbosity :: Int
      , _prefix :: String
      }

data S
    = S
      { _result :: Set Type
      , _visited :: Set Type
      }

$(makeLenses ''R)
$(makeLenses ''S)

instance Monad m => HasTypeParameters (PathT m) where
    pushParam typ action = local (over params (typ :)) action
    withParams action = do
      ps <- view params
      local (over params (const [])) (action ps)

instance HasMessageInfo R where
    verbosity' = verbosity
    prefix' = prefix

-- Monad which maintains type variable bindings and builds a set of supertypes
type PathT m = RWST R () S m

instance DsMonad m => HasVisitedMap (RWST R () S m) where
    unvisited typ action = do
      typ' <- expandType typ
      c <- Set.member typ' <$> use visited
      case c of
        False -> do
          visited %= Set.insert typ'
          action
        _ -> pure ()

instance DsMonad m => HasTypeTraversal (RWST R () S m) where
    doTypeInternal = \typ -> message 1 ("doTypeInternal " ++ show typ) >> local (over prefix' (++ " ")) (doApply typ typ)
    doListT = \typ0 etyp -> message 1 ("doListT " ++ pprint1 typ0) >> doType etyp
    doTupleT = \_ etyp _ -> message 1 ("doTupleT " ++ show etyp) >> doType etyp
    doField = \_t0 _ fi@(FieldInfo {..})  -> message 1 ("doField " ++ show fi) >> doType _fieldType
    doVarT = \_ typ -> message 1 ("doVarT " ++ pprint1 typ) >> result %= Set.insert typ

nonPhantom :: DsMonad m => Name -> m [Type]
nonPhantom tname =
    runQ (reify tname) >>= go
    where
      go :: DsMonad m => Info -> m [Type]
#if MIN_VERSION_template_haskell(2,11,0)
      go (TyConI (DataD _cx _tname binds _mkind _cons _supers)) = mapM (runQ . varT . toName) binds >>= go'
      go (TyConI (NewtypeD _cx _tname binds _mkind _con _supers)) = mapM (runQ . varT . toName) binds >>= go'
#else
      go (TyConI (DataD _cx _tname binds _cons _supers)) = mapM (runQ . varT . toName) binds >>= go'
      go (TyConI (NewtypeD _cx _tname binds _con _supers)) = mapM (runQ . varT . toName) binds >>= go'
#endif
      go (TyConI (TySynD _tname binds _typ)) = mapM (runQ . varT . toName) binds >>= go'
      go x = error $ "th-typegraph:nonPhantom - expecting TyConI DataD/TyConI NewtypeD/TyConI TySynD, but found " ++ show x
      go' :: DsMonad m => [Type] -> m [Type]
      go' ps =
          (Set.toList . view (_1 . result)) <$>
            execRWST (go'' (ConT tname))
              (R {_params = ps, _verbosity = 0, _prefix = "  "})
              (S {_result = Set.empty, _visited = mempty})
      go'' :: DsMonad m => Type -> RWST R () S m ()
      go'' = doType

-- λ> $([t|forall u key proxy s. SPath u key proxy s|] >>= nonPhantom >>= lift . fmap pprint)
-- ["key_0","proxy_0"]
