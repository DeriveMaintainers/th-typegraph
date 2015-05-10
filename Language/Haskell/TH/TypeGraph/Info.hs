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
import Data.Monoid (mempty)
#endif
import Control.Lens -- (makeLenses, view)
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.State (execStateT, StateT)
import Data.List as List (intercalate, map)
import Data.Map as Map (insert, insertWith, Map, toList)
import Data.Set as Set (insert, member, Set, singleton, toList, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.TypeGraph.Core (pprint')
import Language.Haskell.TH.TypeGraph.Expand (E(E), expandType)
import Language.Haskell.TH.TypeGraph.Hints (VertexHint(..), hintType)
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

instance Lift TypeGraphInfo where
    lift (TypeGraphInfo {_typeSet = t, _infoMap = i, _expanded = e, _synonyms = s, _fields = f, _hints = h}) =
        [| TypeGraphInfo {_typeSet = $(lift t),
                          _infoMap = $(lift i),
                          _expanded = $(lift e),
                          _synonyms = $(lift s),
                          _fields = $(lift f),
                          _hints = $(lift h)} |]

emptyTypeGraphInfo :: TypeGraphInfo
emptyTypeGraphInfo = TypeGraphInfo {_typeSet = mempty, _infoMap = mempty, _expanded = mempty, _synonyms = mempty, _fields = mempty, _hints = mempty}

withTypeGraphInfo :: forall m a. DsMonad m => [(TypeGraphVertex, VertexHint)] -> [Type] -> ReaderT TypeGraphInfo m a -> m a
withTypeGraphInfo hintList types action = typeGraphInfo hintList types >>= runReaderT action

-- | Collect the graph information for one type.
typeGraphInfo' :: forall m. DsMonad m => Type -> StateT TypeGraphInfo m ()
typeGraphInfo' typ0 = do
  doType typ0
    where
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

-- | Add a hint to the TypeGraphInfo state and process any type it
-- might contain.
typeGraphHint :: DsMonad m => TypeGraphVertex -> VertexHint -> StateT TypeGraphInfo m ()
typeGraphHint v h = do
  maybe (return ()) typeGraphInfo' (hintType h)
  hints %= Map.insertWith (++) v [h]

-- | Build a TypeGraphInfo value by scanning the supplied types and hints.
typeGraphInfo :: forall m. DsMonad m => [(TypeGraphVertex, VertexHint)] -> [Type] -> m TypeGraphInfo
typeGraphInfo hintList types = flip execStateT emptyTypeGraphInfo $ do
  mapM_ typeGraphInfo' types
  mapM_ (uncurry typeGraphHint) hintList
