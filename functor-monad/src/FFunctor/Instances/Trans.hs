{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module FFunctor.Instances.Trans where

import {-# SOURCE #-} FFunctor

import Control.Applicative.Lift
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer

import Control.Comonad.Env (EnvT(..))
import Control.Comonad.Traced (TracedT(..))
import Control.Comonad.Store (StoreT (..))

instance FFunctor Lift where
  ffmap gh = mapLift gh

instance FFunctor IdentityT where
  ffmap fg = IdentityT . fg . runIdentityT

instance FFunctor (ReaderT e) where
  ffmap fg = ReaderT . fmap fg . runReaderT

instance FFunctor (WriterT m) where
  ffmap fg = WriterT . fg . runWriterT

instance FFunctor (StateT s) where
  ffmap fg = StateT . fmap fg . runStateT

instance FFunctor (EnvT e) where
  ffmap gh (EnvT e g) = EnvT e (gh g)

instance FFunctor (TracedT m) where
  ffmap gh (TracedT g) = TracedT (gh g)

instance FFunctor (StoreT s) where
  ffmap gh (StoreT g s) = StoreT (gh g) s
