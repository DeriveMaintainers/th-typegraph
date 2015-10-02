-- | The HasStack monad used in MIMO to construct lenses that look
-- deep into a record type.  However, it does not involve the Path
-- type mechanism, and is unaware of View instances and other things
-- that modify the type graph.  Lets see how it adapts.
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.TH.TypeGraph.Lens
    ( makeTypeGraphLenses
    , lensNamePairs
    ) where

import Control.Category ((.))
import Control.Lens as Lens (makeLensesFor, view)
import Control.Monad.Readers (MonadReaders, viewPoly)
import Control.Monad.States (MonadStates)
import Control.Monad.Writer (execWriterT, tell)
import Data.Map as Map (keys)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.TypeGraph.Edges (simpleEdges)
import Language.Haskell.TH.TypeGraph.Expand (E(E), ExpandMap)
import Language.Haskell.TH.TypeGraph.Stack (lensNamer)
import Language.Haskell.TH.TypeGraph.TypeGraph (edges, TypeGraph)
import Language.Haskell.TH.TypeGraph.Vertex (etype)
import Prelude hiding ((.))

-- | Generate lenses to access the fields of the row types.  Like
-- Control.Lens.TH.makeLenses, but makes lenses for every field, and
-- instead of removing the prefix '_' to form the lens name it adds
-- the prefix "lens" and capitalizes the first letter of the field.
-- The only reason for this function is backwards compatibility,
-- makeLensesFor should be used instead.
makeTypeGraphLenses :: forall m. (DsMonad m, MonadStates ExpandMap m, MonadReaders TypeGraph m) =>
                       m [Dec]
makeTypeGraphLenses =
    execWriterT $ viewPoly edges >>= mapM doType . map (view etype) . Map.keys . simpleEdges
    where
      doType (E (ConT tname)) = qReify tname >>= doInfo
      doType _ = return ()
      doInfo (TyConI (NewtypeD _ tname _ _ _)) = lensNamePairs namer tname >>= \pairs -> runQ (makeLensesFor pairs tname) >>= tell
      doInfo (TyConI (DataD _ tname _ _ _)) = lensNamePairs namer tname >>= \pairs -> runQ (makeLensesFor pairs tname) >>= tell
      doInfo _ = return ()

namer :: Name -> Name -> Name -> (String, String)
namer _tname _cname fname = (nameBase fname, lensNamer (nameBase fname))

-- | Build the list of pairs used by makeLensesFor.
lensNamePairs :: Quasi m => (Name -> Name -> Name -> (String, String)) -> Name -> m [(String, String)]
lensNamePairs namefn tname =
    qReify tname >>= execWriterT . doInfo
    where
      doInfo (TyConI dec) = doDec dec
      doInfo _ = return ()
      doDec (NewtypeD _ _ _ con _) = doCon con
      doDec (DataD _ _ _ cons _) = mapM_ doCon cons
      doDec (TySynD _ _ _) = return ()
      doDec _ = return ()
      doCon (ForallC _ _ con) = doCon con
      doCon (RecC cname flds) = mapM_ (doField cname) flds
      doCon (NormalC _ _) = return ()
      doCon (InfixC _ _ _) = return ()
      doField cname (fname, _, (ConT fTypeName)) = qReify fTypeName >>= doFieldTypeName cname fname
      doField cname (fname, _, _) = tell [namefn tname cname fname]
      doFieldTypeName _cname _fname (PrimTyConI _ _ _) = return ()
      doFieldTypeName cname fname _ = tell [namefn tname cname fname]
