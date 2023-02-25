{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}

module FMonad.State.Day
  (StateT (..), State, generalize,
   outerState, innerState,
   flift) where

import Control.Monad.Trans.Identity
import Data.Functor.Day ( Day(..), day )
import Data.Functor.Day.Curried ( Curried(Curried) )

import FMonad
import FMonad.Adjoint
import FStrong

newtype StateT s mm x a = StateT
  { runStateT :: Curried s (mm (Day s x)) a }
  deriving (Functor)

type State s = StateT s IdentityT

deriving
  via (AdjointT (Day s) (Curried s) mm)
  instance (Functor s, FFunctor mm) => FFunctor (StateT s mm)

deriving
  via (AdjointT (Day s) (Curried s) mm)
  instance (Functor s, FStrong mm) => FStrong (StateT s mm)

to :: StateT s mm x a -> AdjointT (Day s) (Curried s) mm x a
to = AdjointT . runStateT

from :: AdjointT (Day s) (Curried s) mm x a -> StateT s mm x a
from = StateT . runAdjointT

instance (Functor s, FMonad mm) => FMonad (StateT s mm) where
  fpure :: (Functor x) => x ~> StateT s mm x
  fpure = from . fpure

  fjoin :: (Functor x) => StateT s mm (StateT s mm x) ~> StateT s mm x
  fjoin = from . fjoin . ffmap to . to

flift :: (Functor s, FStrong mm, Functor x)
  => mm x ~> StateT s mm x
flift mm = StateT $ Curried \sf -> fstrength' (day sf mm)

generalize :: (Functor s, FMonad mm, Functor x) => State s x ~> StateT s mm x
generalize = from . fffmap (fpure . runIdentityT) . to

outerState :: (Functor x) => (s0 -> (s0, x a)) -> State ((,) s0) x a
outerState stateX = StateT $ Curried \(s,f) -> 
  let (s',xa) = stateX s
   in fpure (day (s',f) xa)

innerState :: (Functor x) => x (s1 -> (s1, a)) -> State ((->) s1) x a
innerState xState = StateT $
  Curried \f ->
    fpure $ Day id xState $ \s1 state ->
      case state s1 of
        (s1',a) -> f s1' a
