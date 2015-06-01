{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.TH.TypeGraph.Info
    ( TypeGraphInfo
    , emptyTypeGraphInfo
    , typeGraphInfo
    , fields, infoMap, synonyms, typeSet
    ) where

#if __GLASGOW_HASKELL__ < 709
import Data.Monoid (mempty)
#endif
import Control.Lens -- (makeLenses, view)
import Control.Monad.State (execStateT, StateT)
import Data.List as List (intercalate, map)
import Data.Map as Map (insert, insertWith, Map, toList)
import Data.Set as Set (insert, member, Set, singleton, toList, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.TypeGraph.Core (pprint')
import Language.Haskell.TH.TypeGraph.Expand (E(E), expandType)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax (Lift(lift), Quasi(..))

-- | Information collected about the graph implied by the structure of
-- one or more 'Type' values.
data TypeGraphInfo
    = TypeGraphInfo
      { _typeSet :: Set Type
      -- ^ All the types encountered, including embedded types such as the
      -- 'Maybe' and the 'Int' in @Maybe Int@.
      , _infoMap :: Map Name Info
      -- ^ The Info record of all known named types
      , _expanded :: Map Type (E Type)
      -- ^ Map of the expansion of all encountered types
      , _synonyms :: Map (E Type) (Set Name)
      -- ^ The types with all type synonyms replaced with their expansions.
      , _fields :: Map (E Type) (Set (Name, Name, Either Int Name))
      -- ^ Map from field type to field names
      } deriving (Show, Eq, Ord)

instance Ppr TypeGraphInfo where
    ppr (TypeGraphInfo {_typeSet = t, _infoMap = i, _expanded = e, _synonyms = s, _fields = f}) =
        ptext $ intercalate "\n  " ["TypeGraphInfo:", ppt, ppi, ppe, pps, ppf] ++ "\n"
        where
          ppt = intercalate "\n    " ("typeSet:" : concatMap (lines . pprint) (Set.toList t))
          ppi = intercalate "\n    " ("infoMap:" : concatMap (lines . (\ (name, info) -> show name ++ " -> " ++ pprint info)) (Map.toList i))
          ppe = intercalate "\n    " ("expanded:" : concatMap (lines . (\ (typ, (E etyp)) -> pprint typ ++ " -> " ++ pprint etyp)) (Map.toList e))
          pps = intercalate "\n    " ("synonyms:" : concatMap (lines . (\ (typ, ns) -> pprint typ ++ " -> " ++ show ns)) (Map.toList s))
          ppf = intercalate "\n    " ("fields:" : concatMap (lines . (\ (typ, fs) -> pprint typ ++ " -> " ++ show fs)) (Map.toList f))

$(makeLenses ''TypeGraphInfo)

instance Lift TypeGraphInfo where
    lift (TypeGraphInfo {_typeSet = t, _infoMap = i, _expanded = e, _synonyms = s, _fields = f}) =
        [| TypeGraphInfo { _typeSet = $(lift t)
                         , _infoMap = $(lift i)
                         , _expanded = $(lift e)
                         , _synonyms = $(lift s)
                         , _fields = $(lift f)
                         } |]

emptyTypeGraphInfo :: TypeGraphInfo
emptyTypeGraphInfo = TypeGraphInfo {_typeSet = mempty, _infoMap = mempty, _expanded = mempty, _synonyms = mempty, _fields = mempty}

-- | Collect the graph information for one type and all the types
-- reachable from it.
collectTypeInfo :: forall m. DsMonad m => Type -> StateT TypeGraphInfo m ()
collectTypeInfo typ0 = do
  doType typ0
    where
      doType :: Type -> StateT TypeGraphInfo m ()
      doType typ = do
        (s :: Set Type) <- use typeSet
        case Set.member typ s of
          True -> return ()
          False -> do typeSet %= Set.insert typ
                      etyp{-@(E etyp')-} <- expandType typ
                      expanded %= Map.insert typ etyp
                      -- expanded %= Map.insert etyp' etyp -- A type is its own expansion, but we shouldn't need this
                      doType' typ

      doType' :: Type -> StateT TypeGraphInfo m ()
      doType' (ConT name) = do
        info <- qReify name
        infoMap %= Map.insert name info
        doInfo name info
      doType' (AppT typ1 typ2) = doType typ1 >> doType typ2
      doType' ListT = return ()
      doType' (VarT _) = return ()
      doType' (TupleT _) = return ()
      doType' typ = error $ "typeGraphInfo: " ++ pprint' typ

      doInfo :: Name -> Info -> StateT TypeGraphInfo m ()
      doInfo _tname (TyConI dec) = doDec dec
      doInfo _tname (PrimTyConI _ _ _) = return ()
      doInfo _tname (FamilyI _ _) = return () -- Not sure what to do here
      doInfo _ info = error $ "typeGraphInfo: " ++ show info

      doDec :: Dec -> StateT TypeGraphInfo m ()
      doDec (TySynD tname _ typ) = do
        etyp <- expandType (ConT tname)
        synonyms %= Map.insertWith union etyp (singleton tname)
        doType typ
      doDec (NewtypeD _ tname _ constr _) = doCon tname constr
      doDec (DataD _ tname _ constrs _) = mapM_ (doCon tname) constrs
      doDec dec = error $ "typeGraphInfo: " ++ pprint' dec

      doCon :: Name -> Con -> StateT TypeGraphInfo m ()
      doCon tname (ForallC _ _ con) = doCon tname con
      doCon tname (NormalC cname flds) = mapM_ doField (zip (List.map (\n -> (tname, cname, Left n)) ([1..] :: [Int])) (List.map snd flds))
      doCon tname (RecC cname flds) = mapM_ doField (List.map (\ (fname, _, ftype) -> ((tname, cname, Right fname), ftype)) flds)
      doCon tname (InfixC (_, lhs) cname (_, rhs)) = mapM_ doField [((tname, cname, Left 1), lhs), ((tname, cname, Left 2), rhs)]

      doField :: ((Name, Name, Either Int Name), Type) -> StateT TypeGraphInfo m ()
      doField (fld, ftyp) = do
        etyp <- expandType ftyp
        fields %= Map.insertWith union etyp (singleton fld)
        doType ftyp

-- | Build a TypeGraphInfo value by scanning the supplied types
typeGraphInfo :: forall m. DsMonad m => [Type] -> m TypeGraphInfo
typeGraphInfo types = flip execStateT emptyTypeGraphInfo $ mapM_ collectTypeInfo types
