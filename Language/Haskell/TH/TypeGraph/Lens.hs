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
    ( makeLenses'
    ) where

import Control.Applicative
import Control.Category ((.))
import Control.Lens as Lens (Lens', lens, view)
import Control.Monad.Readers (runReaderT)
import Control.Monad.States (MonadStates)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (WriterT, execWriterT, tell)
import Data.Map as Map (keys)
import Data.Set (Set)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.TypeGraph.Edges (GraphEdges, simpleEdges, typeGraphEdges)
import Language.Haskell.TH.TypeGraph.Expand (E(E), ExpandMap)
import Language.Haskell.TH.TypeGraph.Shape (FieldType(..), constructorFieldTypes)
import Language.Haskell.TH.TypeGraph.Stack (execStackT, foldField, lensNamer, StackT)
import Language.Haskell.TH.TypeGraph.TypeInfo (makeTypeInfo)
import Language.Haskell.TH.TypeGraph.Vertex (etype, TGV)
import Prelude hiding ((.))

-- | Generate lenses to access the fields of the row types.  Like
-- Control.Lens.TH.makeLenses, but makes lenses for every field, and
-- instead of removing the prefix '_' to form the lens name it adds
-- the prefix "lens" and capitalizes the first letter of the field.
-- The only reason for this function is backwards compatibility,
-- makeLensesFor should be used instead.
makeLenses' :: forall m. (DsMonad m, MonadStates ExpandMap m) => (Type -> m (Set Type)) -> [Name] -> m [Dec]
makeLenses' extraTypes typeNames =
    execWriterT $ execStackT $ makeTypeInfo (lift . lift . extraTypes) st >>= runReaderT typeGraphEdges >>= \ (g :: GraphEdges TGV) -> (mapM doType . map (view etype) . Map.keys . simpleEdges $ g)
    where
      st = map ConT typeNames

      doType (E (ConT name)) = qReify name >>= doInfo
      doType _ = return ()
      doInfo (TyConI dec@(NewtypeD _ typeName _ con _)) = doCons dec typeName [con]
      doInfo (TyConI dec@(DataD _ typeName _ cons _)) = doCons dec typeName cons
      doInfo _ = return ()
      doCons dec typeName cons = mapM_ (\ con -> mapM_ (foldField (doField typeName) dec con) (constructorFieldTypes con)) cons

      -- (mkName $ nameBase $ tName dec) dec lensNamer) >>= tell
      doField :: Name -> FieldType -> StackT (WriterT [Dec] m) ()
      doField typeName (Named (fieldName, _, fieldType)) =
          doFieldType typeName fieldName fieldType
      doField _ _ = return ()
      doFieldType typeName fieldName (ForallT _ _ typ) = doFieldType typeName fieldName typ
      doFieldType typeName fieldName fieldType@(ConT fieldTypeName) = qReify fieldTypeName >>= doFieldInfo typeName fieldName fieldType
      doFieldType typeName fieldName fieldType = makeLens typeName fieldName fieldType
      doFieldInfo typeName fieldName fieldType (TyConI _fieldTypeDec) = makeLens typeName fieldName fieldType
      doFieldInfo _ _ _ (PrimTyConI _ _ _) = return ()
      doFieldInfo _ _ _ info = error $ "makeLenses - doFieldType: " ++ show info

      makeLens typeName fieldName fieldType =
          do let lensName = mkName (lensNamer (nameBase fieldName))
             sig <- runQ $ sigD lensName (runQ [t|Lens' $(conT typeName) $(pure fieldType)|])
             val <- runQ $ valD (varP lensName) (normalB (runQ [|lens $(varE fieldName) (\ s x -> $(recUpdE [|s|] [ (,) <$> pure fieldName <*> [|x|] ]))|])) []
             return [sig, val] >>= tell
