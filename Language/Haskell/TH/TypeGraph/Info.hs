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
    ( -- * Type and builders
      TypeInfo, startTypes, fields, infoMap, synonyms, typeSet
    , makeTypeInfo
    -- * Update
    , typeVertex
    , typeVertex'
    , fieldVertex
    -- * Query
    , fieldVertices
    , allVertices
    ) where

#if __GLASGOW_HASKELL__ < 709
import Data.Monoid (mempty)
#endif
import Control.Lens -- (makeLenses, view)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (execStateT, StateT)
import Data.List as List (intercalate, map)
import Data.Map as Map (findWithDefault, insert, insertWith, Map, toList)
import Data.Set as Set (empty, insert, map, member, Set, singleton, toList, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax (Lift(lift), Quasi(..))
import Language.Haskell.TH.TypeGraph.Expand (E(E), expandType)
import Language.Haskell.TH.TypeGraph.Prelude (pprint')
import Language.Haskell.TH.TypeGraph.Shape (Field)
import Language.Haskell.TH.TypeGraph.Vertex (TGV(..), TGVSimple(..), etype)

-- | Information collected about the graph implied by the structure of
-- one or more 'Type' values.
data TypeInfo
    = TypeInfo
      { _startTypes :: [Type]
      -- ^ The kernel of types from which the others in _typeSet are discovered
      , _typeSet :: Set Type
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

instance Ppr TypeInfo where
    ppr (TypeInfo {_typeSet = t, _infoMap = i, _expanded = e, _synonyms = s, _fields = f}) =
        ptext $ intercalate "\n  " ["TypeInfo:", ppt, ppi, ppe, pps, ppf] ++ "\n"
        where
          ppt = intercalate "\n    " ("typeSet:" : concatMap (lines . pprint) (Set.toList t))
          ppi = intercalate "\n    " ("infoMap:" : concatMap (lines . (\ (name, info) -> show name ++ " -> " ++ pprint info)) (Map.toList i))
          ppe = intercalate "\n    " ("expanded:" : concatMap (lines . (\ (typ, (E etyp)) -> pprint typ ++ " -> " ++ pprint etyp)) (Map.toList e))
          pps = intercalate "\n    " ("synonyms:" : concatMap (lines . (\ (typ, ns) -> pprint typ ++ " -> " ++ show ns)) (Map.toList s))
          ppf = intercalate "\n    " ("fields:" : concatMap (lines . (\ (typ, fs) -> pprint typ ++ " -> " ++ show fs)) (Map.toList f))

$(makeLenses ''TypeInfo)

instance Lift TypeInfo where
    lift (TypeInfo {_startTypes = st, _typeSet = t, _infoMap = i, _expanded = e, _synonyms = s, _fields = f}) =
        [| TypeInfo { _startTypes = $(lift st)
                    , _typeSet = $(lift t)
                    , _infoMap = $(lift i)
                    , _expanded = $(lift e)
                    , _synonyms = $(lift s)
                    , _fields = $(lift f)
                    } |]

-- | Collect the graph information for one type and all the types
-- reachable from it.
collectTypeInfo :: forall m. DsMonad m => Type -> StateT TypeInfo m ()
collectTypeInfo typ0 = do
  doType typ0
    where
      doType :: Type -> StateT TypeInfo m ()
      doType typ = do
        (s :: Set Type) <- use typeSet
        case Set.member typ s of
          True -> return ()
          False -> do typeSet %= Set.insert typ
                      etyp{-@(E etyp')-} <- expandType typ
                      expanded %= Map.insert typ etyp
                      -- expanded %= Map.insert etyp' etyp -- A type is its own expansion, but we shouldn't need this
                      doType' typ

      doType' :: Type -> StateT TypeInfo m ()
      doType' (ConT name) = do
        info <- qReify name
        infoMap %= Map.insert name info
        doInfo name info
      doType' (AppT typ1 typ2) = doType typ1 >> doType typ2
      doType' ListT = return ()
      doType' (VarT _) = return ()
      doType' (TupleT _) = return ()
      doType' typ = error $ "makeTypeInfo: " ++ pprint' typ

      doInfo :: Name -> Info -> StateT TypeInfo m ()
      doInfo _tname (TyConI dec) = doDec dec
      doInfo _tname (PrimTyConI _ _ _) = return ()
      doInfo _tname (FamilyI _ _) = return () -- Not sure what to do here
      doInfo _ info = error $ "makeTypeInfo: " ++ show info

      doDec :: Dec -> StateT TypeInfo m ()
      doDec (TySynD tname _ typ) = do
        etyp <- expandType (ConT tname)
        synonyms %= Map.insertWith union etyp (singleton tname)
        doType typ
      doDec (NewtypeD _ tname _ constr _) = doCon tname constr
      doDec (DataD _ tname _ constrs _) = mapM_ (doCon tname) constrs
      doDec dec = error $ "makeTypeInfo: " ++ pprint' dec

      doCon :: Name -> Con -> StateT TypeInfo m ()
      doCon tname (ForallC _ _ con) = doCon tname con
      doCon tname (NormalC cname flds) = mapM_ doField (zip (List.map (\n -> (tname, cname, Left n)) ([1..] :: [Int])) (List.map snd flds))
      doCon tname (RecC cname flds) = mapM_ doField (List.map (\ (fname, _, ftype) -> ((tname, cname, Right fname), ftype)) flds)
      doCon tname (InfixC (_, lhs) cname (_, rhs)) = mapM_ doField [((tname, cname, Left 1), lhs), ((tname, cname, Left 2), rhs)]

      doField :: ((Name, Name, Either Int Name), Type) -> StateT TypeInfo m ()
      doField (fld, ftyp) = do
        etyp <- expandType ftyp
        fields %= Map.insertWith union etyp (singleton fld)
        doType ftyp

-- | Build a TypeInfo value by scanning the supplied types
makeTypeInfo :: forall m. DsMonad m => [Type] -> m TypeInfo
makeTypeInfo types =
    execStateT
      (mapM_ collectTypeInfo types)
      (TypeInfo { _startTypes = types
                , _typeSet = mempty
                , _infoMap = mempty
                , _expanded = mempty
                , _synonyms = mempty
                , _fields = mempty})

allVertices :: (Functor m, DsMonad m, MonadReader TypeInfo m) => Maybe Field -> E Type -> m (Set TGV)
allVertices (Just fld) etyp = singleton <$> fieldVertex fld etyp
allVertices Nothing etyp = do
  v <- typeVertex etyp
  vs <- fieldVertices v
  return $ Set.insert (TGV {_vsimple = v, _field = Nothing}) vs

-- | Find the vertices that involve a particular type - if the field
-- is specified it return s singleton, otherwise it returns a set
-- containing a vertex one for the type on its own, and one for each
-- field containing that type.
fieldVertices :: MonadReader TypeInfo m => TGVSimple -> m (Set TGV)
fieldVertices v = do
  fm <- view fields
  let fs = Map.findWithDefault Set.empty (view etype v) fm
  return $ Set.map (\fld' -> TGV {_vsimple = v, _field = Just fld'}) fs

-- | Build a vertex from the given 'Type' and optional 'Field'.
-- vertex :: forall m. (DsMonad m, MonadReader TypeInfo m) => Maybe Field -> E Type -> m TypeGraphVertex
-- vertex fld etyp = maybe (typeVertex etyp) (fieldVertex etyp) fld

-- | Build a non-field vertex
typeVertex :: MonadReader TypeInfo m => E Type -> m TGVSimple
typeVertex etyp = do
  sm <- view synonyms
  return $ TGVSimple {_syns = Map.findWithDefault Set.empty etyp sm, _etype = etyp}

typeVertex' :: MonadReader TypeInfo m => E Type -> m TGV
typeVertex' etyp = do
  v <- typeVertex etyp
  return $ TGV {_vsimple = v, _field = Nothing}

-- | Build a vertex associated with a field
fieldVertex :: MonadReader TypeInfo m => Field -> E Type -> m TGV
fieldVertex fld' etyp = typeVertex etyp >>= \v -> return $ TGV {_vsimple = v, _field = Just fld'}
