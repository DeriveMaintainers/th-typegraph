-- | MonadState without the function dependency @m -> s@.
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Haskell.TH.TypeGraph.HasState
    ( HasState(getState, modifyState)
    ) where

import Control.Monad.Reader (ReaderT)
import Control.Monad.RWS (RWST)
import Control.Monad.State (StateT, get, modify)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (WriterT)

-- | This class allows you to access bits of the State by type,
-- without knowing exactly what the overall state type is.  For
-- example:
--
--   typeGraphEdges :: (DsMonad m,
--                      MonadReader TypeGraph m,
--                      HasState (Set TGV) m,
--                      HasState (Map Type (E Type)) m) => ...
--
-- This will work as long as the two HasState instances exist for
-- whatever the actual State type is.  It still can't reach down
-- into nested StateT monads, you may need to use lift for that.

class HasState s m where
    getState :: m s
    modifyState :: (s -> s) -> m ()

instance Monad m => HasState s (StateT s m) where
    getState = get
    modifyState = modify

instance (Monad m, Monoid w) => HasState s (RWST r w s m) where
    getState = get
    modifyState = modify

instance (Monad m, HasState s m) => HasState s (ReaderT r m) where
    getState = lift getState
    modifyState f = lift $ modifyState f

instance (Monad m, Monoid w, HasState s m) => HasState s (WriterT w m) where
    getState = lift getState
    modifyState f = lift $ modifyState f
