{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}

module FMonad.State.Simple.Outer
  (StateT, State, generalize,
   state, runState, flift) where

import Control.Monad.Trans.Identity ( IdentityT(..) )
import Control.Comonad.Trans.Env
import Control.Monad.Trans.Reader
import Data.Tuple (swap)

import FMonad
import FMonad.Adjoint

type StateT s0 = AdjointT (EnvT s0) (ReaderT s0)
type State s0 = StateT s0 IdentityT

flift :: (FFunctor mm, Functor x)
  => mm x ~> StateT s0 mm x
flift mm = AdjointT $ ReaderT \s0 -> ffmap (EnvT s0) mm

state :: forall s0 x a. (s0 -> (x a, s0)) -> State s0 x a
state stateX = AdjointT $ ReaderT \s0 ->
    case stateX s0 of
        (x, s0') -> IdentityT (EnvT s0' x)

runState :: forall s0 x a. State s0 x a -> s0 -> (x a, s0)
runState stateX = swap . runEnvT . runIdentityT . runReaderT (runAdjointT stateX)