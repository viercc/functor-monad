{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}

module FMonad.State.Lan
  (StateT (..), State, generalize, innerState) where

import Control.Monad.Trans.Identity
import Data.Functor.Kan.Lan
import Data.Functor.Precompose

import FMonad
import FMonad.Adjoint

newtype StateT s mm x a = StateT
  { runStateT :: Precompose s (mm (Lan s x)) a }

deriving
  stock
  instance (Functor s, FFunctor mm, Functor x) => Functor (StateT s mm x)

type State s = StateT s IdentityT

deriving
  via (AdjointT (Lan s) (Precompose s) mm)
  instance (Functor s, FFunctor mm) => FFunctor (StateT s mm)

to :: StateT s mm x a -> AdjointT (Lan s) (Precompose s) mm x a
to = AdjointT . runStateT

from :: AdjointT (Lan s) (Precompose s) mm x a -> StateT s mm x a
from = StateT . runAdjointT

instance (Functor s, FMonad mm) => FMonad (StateT s mm) where
  fpure :: (Functor x) => x ~> StateT s mm x
  fpure = from . fpure

  fjoin :: (Functor x) => StateT s mm (StateT s mm x) ~> StateT s mm x
  fjoin = from . fjoin . ffmap to . to

generalize :: (Functor s, FMonad mm, Functor x) => State s x ~> StateT s mm x
generalize = from . fffmap (fpure . runIdentityT) . to

innerState :: (Functor x) => x (s1 -> (s1, a)) -> State ((,) s1) x a
innerState xState = StateT $
  Precompose $ fpure $ Lan (\(s1,state) -> state s1) xState