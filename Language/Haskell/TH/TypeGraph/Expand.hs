-- | The 'Expanded' class helps keep track of which 'Type' values have
-- been fully expanded to a canonical form.  This lets us use the 'Eq'
-- and 'Ord' relationships on 'Type' and 'Pred' values when reasoning
-- about instance context.  What the 'expandType' function does is use
-- the function from @th-desugar@ to replace occurrences of @ConT name@
-- with the associated 'Type' if @name@ is a declared type synonym
-- @TySynD name _ typ@.  For convenience, a wrapper type 'E' is
-- provided, along with the 'Expanded' instances @E Type@ and @E
-- Pred@.  Now the 'expandType' and 'expandPred' functions can be used
-- to return values of type @E Type@ and @E Pred@ respectively.
--
-- Instances @Expanded Type Type@ and @Expanded Pred Pred@ are
-- provided in "Language.Haskell.TH.Context.Unsafe", for when less
-- type safety is required.

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.Haskell.TH.TypeGraph.Expand
    ( E(E, unE)
    , ExpandMap
    , HasExpandMap(expandMap)
    , expandType
    , expandPred
    , expandClassP
    ) where

-- import Control.Monad.States (MonadStates(get), modify)
import Control.Monad.State (MonadState)
import Control.Lens
import Data.Map as Map (Map, lookup, insert)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar as DS (DsMonad, dsType, expand, typeToTH)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax -- (Lift(lift))
import Prelude hiding (pred)

-- | A concrete type used to mark type which have been expanded
newtype E a = E {unE :: a} deriving (Eq, Ord, Show)

instance Ppr a => Ppr (E a) where
    ppr (E x) = ppr x

instance Lift (E Type) where
    lift etype = [|E $(lift (unE etype))|]

-- | The state type used to memoize expansions.
type ExpandMap = Map Type (E Type)

class HasExpandMap s where expandMap :: Lens' s ExpandMap

instance HasExpandMap ExpandMap where expandMap = id

-- | Apply the th-desugar expand function to a 'Type' and mark it as expanded.
expandType :: (DsMonad m, MonadState s m, HasExpandMap s)  => Type -> m (E Type)
expandType typ = do
  use expandMap >>= maybe expandType' return . Map.lookup typ
    where
      expandType' =
          do e <- E <$> DS.typeToTH <$> (DS.dsType typ >>= DS.expand)
             expandMap %= (Map.insert typ e)
             return e

-- | Apply the th-desugar expand function to a 'Pred' and mark it as expanded.
-- Note that the definition of 'Pred' changed in template-haskell-2.10.0.0.
expandPred :: (DsMonad m, MonadState s m, HasExpandMap s)  => Type -> m (E Type)
expandPred = expandType

-- | Expand a list of 'Type' and build an expanded 'ClassP' 'Pred'.
expandClassP :: forall s m. (DsMonad m, MonadState s m, HasExpandMap s)  => Name -> [Type] -> m (E Type)
expandClassP className typeParameters = (expandType $ foldl AppT (ConT className) typeParameters) :: m (E Type)
