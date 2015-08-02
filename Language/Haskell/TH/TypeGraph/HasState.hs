-- | MonadState without the function dependency @m -> s@.
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Haskell.TH.TypeGraph.HasState
    ( HasState(getState, modifyState)
    , HasReader(ask, local)
    ) where

import Control.Monad.Reader (ReaderT)
import qualified Control.Monad.Reader as M (ask, local)
import Control.Monad.RWS (RWST)
import Control.Monad.State (StateT, evalStateT, get, modify)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (runWriterT, WriterT)

-- | This class allows you to access bits of the State by type,
-- without knowing exactly what the overall state type is.  For
-- example:
-- @
--   typeGraphEdges :: (DsMonad m,
--                      MonadReader TypeGraph m,
--                      HasState Foo m,
--                      HasState Bar m) => ...
-- @
-- This will work as long as the two HasState instances exist for
-- whatever the actual State type is:
-- @
--   Data S = S {_foo :: Foo, _bar :: Bar}
--   $(makeLenses ''S)
--
--   instance Monad m => HasState Foo (StateT S m) where
--      getState = use foo
--      modifyState f = foo %= f
--
--   instance Monad m => HasState Bar (StateT S m) where
--      getState = use bar
--      modifyState f = bar %= f
-- @
-- Now you can say
-- @
--   evalState (return (getState, getState) :: (Foo, Bar)) (S foo0, bar0)
-- @
-- You can even write instances to reach down into nested StateT's as
-- long as you know the exact type you are reaching down through, in
-- this case StateT Bar:
-- @
--   Instance HasState Foo m => HasState Foo (StateT Baz m) where
--     getState = lift getState
--     modifyState f = lift $ modifyState f
-- @

class Monad m => HasState s m where
    getState :: m s
    modifyState :: (s -> s) -> m ()

instance Monad m => HasState s (StateT s m) where
    getState = get
    modifyState = modify

instance (Monad m, HasState s m) => HasState s (ReaderT r m) where
    getState = lift getState
    modifyState f = lift $ modifyState f

instance (Monad m, Monoid w, HasState s m) => HasState s (WriterT w m) where
    getState = lift getState
    modifyState f = lift $ modifyState f

instance (Monad m, Monoid w) => HasState s (RWST r w s m) where
    getState = get
    modifyState = modify

-- | Similar idea for ReaderT.  Experimenting with using the same
-- names as MonadReader (ask and local) - if it works nicely I may
-- change HasState to do the same.
class Monad m => HasReader r m where
    ask :: m r
    local :: (r -> r) -> m a -> m a

instance Monad m => HasReader r (ReaderT r m) where
    ask = M.ask
    local = M.local

instance (Monad m, HasReader r m) => HasReader r (StateT s m) where
    ask = lift ask
    local f action = get >>= lift . local f . evalStateT action

instance (Monad m, Monoid w, HasReader r m) => HasReader r (WriterT w m) where
    ask = lift ask
    local f action = lift (local f (runWriterT action >>= return . fst))

{-
instance (Monad m, HasReader [StackElement] m) => HasReader [StackElement] (ReaderT Foo m) where
    ask = lift ask
    local f action = MTL.ask >>= runReaderT (local f (lift action))

instance (Quasi m, Monoid w) => HasStack (RWST [StackElement] w s m) where
    withStack f = ask >>= f
    push fld con dec action = local (\ stk -> StackElement fld con dec : stk) action
-}
