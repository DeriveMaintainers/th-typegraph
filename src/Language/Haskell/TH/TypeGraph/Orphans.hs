{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS -fno-warn-unused-imports -fno-warn-orphans #-}

module Language.Haskell.TH.TypeGraph.Orphans where

import qualified Data.Graph.Inductive as G
import Data.Proxy (Proxy(Proxy))
import Data.SafeCopy (base, contain, deriveSafeCopy, SafeCopy(errorTypeName, getCopy, kind, putCopy, version))
import Data.Serialize (label, Serialize(..))
import Data.Set as Set (Set, toList)
import Data.Time (UTCTime(..), Day(ModifiedJulianDay), toModifiedJulianDay, DiffTime)
import Data.UserId (UserId(..))
import Extra.Orphans ()
import Instances.TH.Lift ()
import Language.Haskell.TH (ExpQ, Loc(..), location, Name, NameSpace, Type)
import Language.Haskell.TH.Instances ({-instance Lift Loc-})
import Language.Haskell.TH.Lift (deriveLift, lift)
import Language.Haskell.TH.Ppr (Ppr(ppr))
import Language.Haskell.TH.PprLib (hcat, ptext, vcat)
import Language.Haskell.TH.Syntax (ModName(..), NameFlavour(..), OccName(..), PkgName(..))

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

$(deriveSafeCopy 0 'base ''OccName)
$(deriveSafeCopy 0 'base ''NameSpace)
$(deriveSafeCopy 0 'base ''PkgName)
$(deriveSafeCopy 0 'base ''ModName)
$(deriveSafeCopy 0 'base ''NameFlavour)
$(deriveSafeCopy 0 'base ''Name)
$(deriveSafeCopy 1 'base ''Loc)
