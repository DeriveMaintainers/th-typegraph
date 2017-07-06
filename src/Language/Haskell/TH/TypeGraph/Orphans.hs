{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS -fno-warn-unused-imports -fno-warn-orphans #-}

module Language.Haskell.TH.TypeGraph.Orphans where

import Data.Aeson (FromJSON(parseJSON), Value(Null), ToJSON(toJSON))
#if MIN_VERSION_aeson(1,0.0)
import Data.Aeson (ToJSONKey, FromJSONKey)
#endif
#if !MIN_VERSION_aeson(0,11,0)
import Data.Aeson.Types (typeMismatch)
#endif
import qualified Data.Graph.Inductive as G
import Data.Proxy (Proxy(Proxy))
import Data.Set as Set (Set, toList)
import Data.Time (UTCTime(..), Day(ModifiedJulianDay), toModifiedJulianDay, DiffTime)
import Data.UserId (UserId(..))
import Instances.TH.Lift ()
import Language.Haskell.TH (ExpQ, Loc(..), location, Name, NameSpace, Type)
import Language.Haskell.TH.Instances ({-instance Lift Loc-})
import Language.Haskell.TH.Lift (deriveLift, lift)
import Language.Haskell.TH.Ppr (Ppr(ppr))
import Language.Haskell.TH.PprLib (hcat, ptext, vcat)
import Language.Haskell.TH.Syntax (ModName(..), NameFlavour(..), OccName(..), PkgName(..))
import Data.SafeCopy (base, contain, deriveSafeCopy, SafeCopy(errorTypeName, getCopy, kind, putCopy, version))
import Data.Serialize (label, Serialize(..))

#if !MIN_VERSION_aeson(0,11,0)
-- Backport the JSON instances from aeson-0.11.
instance ToJSON (Proxy a) where
   toJSON _ = Null
   {-# INLINE toJSON #-}

instance FromJSON (Proxy a) where
    {-# INLINE parseJSON #-}
    parseJSON Null = pure Proxy
    parseJSON v    = typeMismatch "Proxy" v
#endif

instance Ppr () where
    ppr () = ptext "()"

-- | 'Int' is the 'Data.Path.Index.ContainerKey' type for all lists, so
-- we need to make sure all the required instances exist.
instance Ppr Int where
    ppr = ptext . show

instance Ppr (Set Type, Set Type) where
    ppr (extra, missing) = vcat [ptext "extra:", ppr extra, ptext "missing:", ppr missing]

instance Ppr (Set Type) where
    ppr s = hcat [ptext "Set.fromList [", ppr (Set.toList s), ptext "]"]

instance SafeCopy (Proxy t) where
      putCopy Proxy = contain (do { return () })
      getCopy = contain (label "Data.Proxy.Proxy:" (pure Proxy))
      version = 0
      kind = base
      errorTypeName _ = "Data.Proxy.Proxy"

$(deriveSafeCopy 0 'base ''OccName)
$(deriveSafeCopy 0 'base ''NameSpace)
$(deriveSafeCopy 0 'base ''PkgName)
$(deriveSafeCopy 0 'base ''ModName)
$(deriveSafeCopy 0 'base ''NameFlavour)
$(deriveSafeCopy 0 'base ''Name)
$(deriveSafeCopy 1 'base ''Loc)

instance Serialize UTCTime where
    get = uncurry UTCTime <$> get
    put (UTCTime day time) = put (day, time)

instance Serialize Day where
    get = ModifiedJulianDay <$> get
    put = put . toModifiedJulianDay

instance Serialize DiffTime where
    get = fromRational <$> get
    put = put . toRational

#if MIN_VERSION_aeson(1,0,0)
instance FromJSONKey UserId
instance ToJSONKey UserId
#endif

deriving instance Serialize UserId
deriving instance Serialize Loc

$(deriveLift ''UserId)

$(deriveLift ''G.Gr)
$(deriveLift ''G.NodeMap)
