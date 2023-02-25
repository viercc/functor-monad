{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}

module FMonad.State.Ran
  (StateT (..), State, generalize, innerState) where

import Control.Monad.Trans.Identity
import Data.Functor.Kan.Ran
import Data.Functor.Precompose

import FMonad
import FMonad.Adjoint

newtype StateT s mm x a = StateT
  { runStateT :: Ran s (mm (Precompose s x)) a }
  deriving (Functor)

type State s = StateT s IdentityT

deriving
  via (AdjointT (Precompose s) (Ran s) mm)
  instance (Functor s, FFunctor mm) => FFunctor (StateT s mm)

to :: StateT s mm x a -> AdjointT (Precompose s) (Ran s) mm x a
to = AdjointT . runStateT

from :: AdjointT (Precompose s) (Ran s) mm x a -> StateT s mm x a
from = StateT . runAdjointT

instance (Functor s, FMonad mm) => FMonad (StateT s mm) where
  fpure :: (Functor x) => x ~> StateT s mm x
  fpure = from . fpure

  fjoin :: (Functor x) => StateT s mm (StateT s mm x) ~> StateT s mm x
  fjoin = from . fjoin . ffmap to . to

generalize :: (Functor s, FMonad mm, Functor x) => State s x ~> StateT s mm x
generalize = from . fffmap (fpure . runIdentityT) . to

innerState :: (Functor x) => x (s1 -> (s1, a)) -> State ((->) s1) x a
innerState xState = StateT $
  Ran \f ->
    fpure $ Precompose $ fmap (\state s1 -> case state s1 of (s1', a) -> f a s1') xState
