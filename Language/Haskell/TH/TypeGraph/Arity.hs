-- | Function to compute the arity or kind of a Type, the number of
-- type parameters that need to be applied to get a concrete type.
module Language.Haskell.TH.TypeGraph.Arity
    ( typeArity
    ) where

import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.Syntax (Quasi(qReify))
import Language.Haskell.TH.TypeGraph.Prelude (pprint')

-- | Compute the arity of a type - the number of type parameters that
-- must be applied to it in order to obtain a concrete type.  I'm not
-- quite sure I understand the relationship between this and 'freeTypeVars'.
typeArity :: Quasi m => Type -> m Int
typeArity (ForallT _ _ typ) = typeArity typ -- Shouldn't a forall affect the arity?
typeArity ListT = return 1
typeArity (TupleT n) = return n
typeArity (VarT _) = return 1
typeArity (AppT t _) = typeArity t >>= \ n -> return $ n - 1
typeArity (ConT name) = qReify name >>= infoArity
    where
      infoArity (TyConI dec) = decArity dec
      infoArity (PrimTyConI _ _ _) = return 0
      infoArity (FamilyI dec _) = decArity dec
      infoArity info = error $ "typeArity - unexpected: " ++ pprint' info
      decArity (DataD _ _ vs _ _) = return $ length vs
      decArity (NewtypeD _ _ vs _ _) = return $ length vs
      decArity (TySynD _ vs t) = typeArity t >>= \ n -> return $ n + length vs
      decArity (FamilyD _ _ vs _mk) = return $ {- not sure what to do with the kind mk here -} length vs
      decArity dec = error $ "decArity - unexpected: " ++ show dec
typeArity typ = error $ "typeArity - unexpected type: " ++ show typ
