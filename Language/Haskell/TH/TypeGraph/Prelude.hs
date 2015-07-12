{-# LANGUAGE TupleSections #-}
module Language.Haskell.TH.TypeGraph.Prelude
    ( listen_
    , pass_
    ) where

import Control.Monad.Writer (listen, MonadWriter, pass)

-- | Simplified Writer monad functions
listen_ :: MonadWriter w m => m w
listen_ = snd <$> listen (return ())

pass_ :: MonadWriter w m => m (w -> w) -> m ()
pass_ f = pass (((),) <$> f)
