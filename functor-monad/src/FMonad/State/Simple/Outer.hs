{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module FMonad.State.Simple.Outer
  (StateT(..), flift, 
   fromAdjointT, toAdjointT,

   State,
   state, runState, 
  ) where

import Control.Monad.Trans.Identity ( IdentityT(..) )
import Control.Comonad.Trans.Env
import Control.Monad.Trans.Reader
import Data.Tuple (swap)
import Data.Coerce (coerce)

import FMonad
import FMonad.Adjoint

newtype StateT s0 mm x a = StateT { runStateT :: s0 -> mm (EnvT s0 x) a }
   deriving (FFunctor, FMonad) via (AdjointT (EnvT s0) (ReaderT s0) mm)
type State s0 = StateT s0 IdentityT

deriving
  stock instance (FFunctor mm, Functor x) => Functor (StateT s0 mm x)

fromAdjointT :: AdjointT (EnvT s0) (ReaderT s0) mm x ~> StateT s0 mm x
fromAdjointT =  coerce

toAdjointT :: StateT s0 mm x ~> AdjointT (EnvT s0) (ReaderT s0) mm x
toAdjointT = coerce

flift :: (FFunctor mm, Functor x)
  => mm x ~> StateT s0 mm x
flift mm = StateT $ \s0 -> ffmap (EnvT s0) mm

state :: forall s0 x mm a. (FMonad mm, Functor x) => (s0 -> (x a, s0)) -> StateT s0 mm x a
state stateX = StateT \s0 ->
    let (x, s0') = stateX s0
     in fpure (EnvT s0' x)

runState :: forall s0 x a. State s0 x a -> s0 -> (x a, s0)
runState stateX = swap . runEnvT . runIdentityT . runStateT stateX