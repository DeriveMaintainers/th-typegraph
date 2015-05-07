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
    , expanded, fields, hints, infoMap, synonyms, typeSet
    , withTypeGraphInfo
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>))
import Data.Monoid (mempty)
#endif
import Control.Lens -- (makeLenses, view)
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.State (execStateT, StateT)
import Data.List as List (intercalate, map)
import Data.Map as Map (elems, fromListWith, insert, insertWith, Map, toList)
import Data.Maybe (mapMaybe)
import Data.Set as Set (insert, member, Set, singleton, toList, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.TypeGraph.Core (pprint')
import Language.Haskell.TH.TypeGraph.Expand (E(E), expandType)
import Language.Haskell.TH.TypeGraph.Hints (VertexHint(..))
import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (ptext)
import Language.Haskell.TH.Syntax (Lift(lift), Quasi(..))

-- | Information collected about the graph implied by the structure of
-- one or more 'Type' values.
data TypeGraphInfo
    = TypeGraphInfo
      { _typeSet :: Set Type
      -- All the types encountered, including embedded types such as the
      -- 'Maybe' and the 'Int' in @Maybe Int@.
      , _infoMap :: Map Name Info
      -- The Info record of all known named types
      , _expanded :: Map Type (E Type)
      -- The types with all type synonyms replaced with their expansions.
      , _synonyms :: Map (E Type) (Set Name)
      -- Map from field type to field names
      , _fields :: Map (E Type) (Set (Name, Name, Either Int Name))
{-
      -- Map from type name to the field names that type contains
      , _decfields :: Map Name (Set (Name, Name, Either Int Name))
      -- Information about record fields which contain a given type
      , _edges :: GraphEdges TypeGraphVertex
-}
      -- The edges of the "has this subtype" graph.  A type has
      -- subtypes via either type application ('AppT'), field type
      -- ('StrictType', 'VarStrictType') or the 'VertexHint'
      -- mechanism.
      , _hints :: Map TypeGraphVertex [VertexHint]
      } deriving (Show, Eq, Ord)

instance Ppr TypeGraphInfo where
    ppr (TypeGraphInfo {_typeSet = t, _infoMap = i, _expanded = e, _synonyms = s, _fields = f, _hints = h}) =
        ptext $ intercalate "\n  " ["TypeGraphInfo:", ppt, ppi, ppe, pps, ppf, pph] ++ "\n"
        where
          ppt = intercalate "\n    " ("typeSet:" : concatMap (lines . pprint) (Set.toList t))
          ppi = intercalate "\n    " ("infoMap:" : concatMap (lines . (\ (name, info) -> show name ++ " -> " ++ pprint info)) (Map.toList i))
          ppe = intercalate "\n    " ("expanded:" : concatMap (lines . (\ (typ, (E etyp)) -> pprint typ ++ " -> " ++ pprint etyp)) (Map.toList e))
          pps = intercalate "\n    " ("synonyms:" : concatMap (lines . (\ (E etyp, ns) -> pprint etyp ++ " -> " ++ show ns)) (Map.toList s))
          ppf = intercalate "\n    " ("fields:" : concatMap (lines . (\ (E etyp, fs) -> pprint etyp ++ " -> " ++ show fs)) (Map.toList f))
          pph = intercalate "\n    " ("hints:" : concatMap (lines . (\ (v, hs) -> pprint v ++ " -> " ++ intercalate " " (map pprint hs))) (Map.toList h))

$(makeLenses ''TypeGraphInfo)

emptyTypeGraphInfo :: TypeGraphInfo
emptyTypeGraphInfo = TypeGraphInfo {_typeSet = mempty, _infoMap = mempty, _expanded = mempty, _synonyms = mempty, _fields = mempty, _hints = mempty}

withTypeGraphInfo :: forall m a. DsMonad m => [(TypeGraphVertex, VertexHint)] -> [Type] -> ReaderT TypeGraphInfo m a -> m a
withTypeGraphInfo hintList types action = typeGraphInfo hintList types >>= runReaderT action

-- | Build a TypeGraphInfo value by scanning the supplied types and hints.
typeGraphInfo :: forall m. DsMonad m => [(TypeGraphVertex, VertexHint)] -> [Type] -> m TypeGraphInfo
typeGraphInfo hintList types = flip execStateT emptyTypeGraphInfo $ do
  hints .= Map.fromListWith (++) (List.map (\ (n, h) -> (n, [h])) hintList)
  hintTypes <- (mapMaybe hintType . concat . Map.elems) <$> use hints
  mapM_ doType (types ++ hintTypes)
    where
      hintType :: VertexHint -> Maybe Type
      hintType (Divert x) = Just x
      hintType (Extra x) = Just x
      hintType _ = Nothing

      doType :: Type -> StateT TypeGraphInfo m ()
      doType typ = do
        (s :: Set Type) <- use typeSet
        case Set.member typ s of
          True -> return ()
          False -> do typeSet %= Set.insert typ
                      etyp <- expandType typ
                      expanded %= Map.insert typ etyp
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
        etyp <- expandType typ
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
        expanded %= Map.insert ftyp etyp
        fields %= Map.insertWith union etyp (singleton fld)
        doType ftyp

#if 0
  (ex :: Map Type (E Type)) <- findExpanded types'
  (sy :: Map (E Type) (Set Name)) <-
      -- Build the type synonym map and then expand the types in its
      -- keys.  This will collapse some of the nodes if they differed
      -- only in the use of synonyms.
      findSynonyms types' >>= return . Map.fromListWith union . List.map (\ (typ, names) -> (expand ex typ, names))  . Map.toList
  fl <- findFields types' >>= return . Map.fromListWith union . List.map (\ (typ, names) -> (expand ex typ, names))  . Map.toList
  -- ed <- findEdges types' ex sy -- >>= return . Map.fromListWith union . List.map (\ (typ, dests) -> (expand ex typ, Set.map (expand ex) dests)) . Map.toList
  let etypes' = Set.fromList $ List.map (expand ex) (Set.toList types')
  return $ TypeGraphInfo { _expanded = ex
                         , _synonyms = sy
                         , _fields = fl
                         , _typeSet = etypes'
                         , _hints =  Map.fromListWith (++) (List.map (\ (n, h) -> (n, [h])) hintList)
                         }
      where expand ex typ = let Just etyp = Map.lookup typ ex in etyp
#endif

#if 0
-- | This is now the only function that actually recurses through the
-- type structure.  It collects the set of all accessable types.
scanTypes :: forall m. DsMonad m => [Type] -> StateT TypeGraphInfo m ()
scanTypes types =
    mapM doType types
    where
      doType :: Type -> StateT (Set Type) m ()
      doType typ = do
        (s :: Set Type) <- get
        case Set.member typ s of
          True -> return ()
          False -> modify (\ (ts, im) -> (Set.insert typ ts, im)) >> doType' typ

      doType' :: Type -> StateT (Set Type) m ()
      doType' (ConT name) = qReify name >>= \info -> modify (\ (ts, im) -> (ts, Map.insert name info im)) >> doInfo name
      doType' (AppT typ1 typ2) = doType typ1 >> doType typ2
      doType' ListT = return ()
      doType' (VarT _) = return ()
      doType' (TupleT _) = return ()
      doType' typ = error $ "scanTypes: " ++ show typ

      doInfo :: Name -> Info -> StateT (Set Type) m ()
      doInfo _tname (TyConI dec) = doDec dec
      doInfo _tname (PrimTyConI _ _ _) = return ()
      doInfo _tname (FamilyI _ _) = return () -- Not sure what to do here
      doInfo _ info = error $ "scanTypes: " ++ show info

      doDec :: Dec -> StateT (Set Type) m ()
      doDec (TySynD _ _ typ) = doType typ
      doDec (NewtypeD _ _ _ constr _) = doCon constr
      doDec (DataD _ _ _ constrs _) = mapM_ doCon constrs
      doDec dec = error $ "scanTypes: " ++ pprint' dec

      doCon :: Con -> StateT (Set Type) m ()
      doCon (ForallC _ _ con) = doCon con
      doCon (NormalC _ flds) = mapM_ doField (zip (List.map Left ([1..] :: [Int])) (List.map snd flds))
      doCon (RecC _ flds) = mapM_ doField (List.map (\ (fname, _, ftype) -> (Right fname, ftype)) flds)
      doCon (InfixC (_, lhs) _ (_, rhs)) = mapM_ doField [(Left 1, lhs), (Left 2, rhs)]

      doField :: (Either Int Name, Type) -> StateT (Set Type) m ()
      doField (_, ftyp) = doType ftyp

-- | Discover the types with all type synonyms fully expanded.
findExpanded :: DsMonad m => Set Type -> m (Map Type (E Type))
findExpanded types =
    execStateT (mapM (\typ -> expandType typ >>= \etyp -> modify (Map.insert typ etyp)) (Set.toList types)) mempty

-- | Discover the type synonyms
findSynonyms :: DsMonad m => Set Type -> m (Map Type (Set Name))
findSynonyms types =
    execStateT (mapM_ doType (Set.toList types)) mempty
    where
      doType (ConT name) = qReify name >>= doInfo
      doType (AppT typ1 typ2) = doType typ1 >> doType typ2
      doType _ = return ()
      doInfo (TyConI dec) = doDec dec
      doInfo _ = return ()
      doDec (TySynD tname _ typ) = modify (Map.insertWith union typ (singleton tname))
      doDec _ = return ()

-- | Discover the field types
findFields :: DsMonad m => Set Type -> m (Map Type (Set (Name, Name, Either Int Name)))
findFields types =
    execStateT (mapM_ doType (Set.toList types)) mempty
    where
      doType (ConT name) = qReify name >>= doInfo
      doType (AppT typ1 typ2) = doType typ1 >> doType typ2
      doType _ = return ()

      doInfo (TyConI dec) = doDec dec
      doInfo _ = return ()

      doDec (NewtypeD _ tname _ constr _) = doCon tname constr
      doDec (DataD _ tname _ constrs _) = mapM_ (doCon tname) constrs
      doDec _ = return ()

      doCon tname (ForallC _ _ con) = doCon tname con
      doCon tname (NormalC cname flds) = mapM_ (doField tname cname) (zip (List.map Left ([1..] :: [Int])) (List.map snd flds))
      doCon tname (RecC cname flds) = mapM_ (doField tname cname) (List.map (\ (fname, _, ftype) -> (Right fname, ftype)) flds)
      doCon tname (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname cname) [(Left 1, lhs), (Left 2, rhs)]

      doField tname cname (fname, ftyp) = modify (Map.insertWith union ftyp (singleton (tname, cname, fname)))
#endif

instance Lift TypeGraphInfo where
    lift (TypeGraphInfo {_typeSet = t, _infoMap = i, _expanded = e, _synonyms = s, _fields = f, _hints = h}) =
        [| TypeGraphInfo {_typeSet = $(lift t),
                          _infoMap = $(lift i),
                          _expanded = $(lift e),
                          _synonyms = $(lift s),
                          _fields = $(lift f),
                          _hints = $(lift h)} |]
