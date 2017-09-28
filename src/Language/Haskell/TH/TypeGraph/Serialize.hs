{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.TH.TypeGraph.Serialize
    ( deriveSerialize
    ) where

import Language.Haskell.TH

import Data.Serialize
import Data.Set (toList)
import Language.Haskell.TH.Lift (lift)
import Language.Haskell.TH.TypeGraph.Constraints (deriveConstraints, withBindings)
import Language.Haskell.TH.TypeGraph.TypeTraversal (toName)

deriveSerialize :: TypeQ -> Q [Dec]
deriveSerialize typq = do
  typq >>= goType
    where
      goType :: Type -> Q [Dec]
      goType typ0 = (: []) <$> goApply typ0 (decompose typ0)

      goApply :: Type -> [Type] -> Q Dec
      goApply typ0 (ConT tname : vals) =
          reify tname >>= goInfo typ0 tname vals
      goApply typ0 (typ : _vals) =
          error ("deriveSerialize - unexpected type " ++ show typ ++ " (in " ++ show typ0 ++ ")")

      goInfo :: Type -> Name -> [Type] -> Info -> Q Dec
      goInfo typ0 _tname vals (TyConI (TySynD _ vars typ)) =
          withBindings vals vars (\subst -> goApply typ0 (decompose (subst typ)))
#if MIN_VERSION_template_haskell(2,11,0)
      goInfo _typ0 tname vals (TyConI (DataD _ _ vars _ cons _)) =
#else
      goInfo _typ0 tname vals (TyConI (DataD _ _ vars cons _)) =
#endif
          withBindings vals vars (\subst -> goClauses tname vals vars (zip [0..] cons) subst)
#if MIN_VERSION_template_haskell(2,11,0)
      goInfo _typ0 tname vals (TyConI (NewtypeD _ _ vars _ con _)) =
#else
      goInfo _typ0 tname vals (TyConI (NewtypeD _ _ vars con _)) =
#endif
          withBindings vals vars (\subst -> goClauses tname vals vars [(0, con)] subst)
#if MIN_VERSION_template_haskell(2,11,0)
      goInfo _typ0 tname vals (FamilyI (DataFamilyD famname vars _mk) _insts) =
#else
      goInfo _typ0 tname vals (FamilyI (FamilyD DataFam famname vars _mk) _insts) =
#endif
        withBindings vals vars
          (\subst -> do let typ = subst (compose (ConT famname : fmap (VarT . toName) vars))
                        error "deriveSerialize - FamilyD")
      goInfo _typ0 _tname _vals info =
          error ("deriveSerialize - unexpected info: " ++ show info)

      goClauses :: Name -> [Type] -> [TyVarBndr] -> [(Int, Con)] -> (Type -> Type) -> Q Dec
      goClauses tname vals vars cons subst = do
          let -- Extend the value list to ensure the resulting type is monomorphic
              vals' = map subst vals ++ map (VarT . toName) (drop (length vals) vars)
              putFun = funD 'put (map (\(tag, con) -> do
                                         (conName, fnames) <- conInfo con
                                         clause [conPat fnames (tag, con)]
                                                (normalB (conExp cons tag conName fnames))
                                                []) cons)
              getFun = funD 'get [clause [] (normalB [|$(if length cons > 1
                                                         then [|getWord8|]
                                                         else [|return 0|]) >>= \i ->
                                                       $(caseE [|i|] (map conGet cons))|]) []]
          constraints <- toList <$> deriveConstraints 0 ''Serialize tname vals'
          instanceD
            (pure constraints)
            (appT (conT ''Serialize) (foldl1 appT (conT tname : map pure vals')))
            [putFun, getFun]
      conPat fnames (_, NormalC name _) = conP name (map varP fnames)
      conPat fnames (_, RecC name _) = conP name (map varP fnames)
      conPat fnames (_, InfixC lhs name rhs) = conP name (map varP fnames)
      conPat fnames (tag, ForallC _ _ con) = conPat fnames (tag, con)

      conExp cons tag cname fnames =
          doSeq $ (if length cons > 1 then [ [|putWord8 $(lift tag)|] ] else []) ++
                  map (\fname -> [|put $(varE fname)|]) fnames
      conGet :: (Int, Con) -> MatchQ
      conGet (n, ForallC _ _ con) = conGet (n, con)
      conGet (n, NormalC name sts) =     match (litP (integerL (fromIntegral n))) (normalB $ doApp $ ([|pure $(conE name)|] : map (const [|get|]) sts)) []
      conGet (n, RecC name vsts) =       match (litP (integerL (fromIntegral n))) (normalB $ doApp $ ([|pure $(conE name)|] : map (const [|get|]) vsts)) []
      conGet (n, InfixC lhs name rhs) =  match (litP (integerL (fromIntegral n))) (normalB $ doApp $ ([|pure $(conE name)|] : map (const [|get|]) [lhs, rhs])) []

      doSeq es = foldl1 (\e1 e2 -> [|$e1 >> $e2|]) es
      doApp es = foldl1 (\e1 e2 -> [|$e1 <*> $e2|]) es

      conInfo (NormalC name sts) = (name,) <$> mapM (\(_, n) -> newName ("a" ++ show n)) (zip sts [1..])
      conInfo (RecC name vsts) = (name,) <$> mapM (\(_, n) -> newName ("a" ++ show n)) (zip vsts [1..])
      conInfo (InfixC lhs name rhs) = (name,) <$> mapM (\n -> newName ("a" ++ show n)) [1, 2]
      conInfo (ForallC _ _ con) = conInfo con

decompose :: Type -> [Type]
decompose t0 = go t0 []
    where go (AppT t1 t2) ts = go t1 (t2 : ts)
          go t ts = t : ts

compose :: [Type] -> Type
compose types = foldl1 AppT types

data Sample alpha  =  First
                   |  Second alpha alpha
                   |  Third alpha

instance Serialize a => Serialize (Sample a)
    where put (First) = putWord8 0
          put (Second a1_0 a2_1) = putWord8 1 >> (put a1_0 >> put a2_1)
          put (Third a1_2) = putWord8 2 >> put a1_2
          get = getWord8 >>= (\i_3 -> case i_3 of
                                        0 -> pure First
                                        1 -> (pure Second <*> get) <*> get
                                        2 -> pure Third <*> get)

-- test = putStrLn $(deriveSerialize [t|Sample|] >>= lift . pprint)
