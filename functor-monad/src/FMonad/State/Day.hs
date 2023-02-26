{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}

module FMonad.State.Day
  (StateT, State,
   flift,
   toOuter, fromOuter, toInner, fromInner,
   generalize) where

import Control.Monad.Trans.Identity
import Data.Functor.Day ( Day(..), day )
import Data.Functor.Day.Curried ( Curried(Curried) )

import FMonad
import FMonad.Adjoint
import FStrong

import qualified FMonad.State.Simple.Inner as Simple.Inner
import qualified FMonad.State.Simple.Outer as Simple.Outer

import Data.Functor.Day.Extra

type StateT s = AdjointT (Day s) (Curried s)
type State s = StateT s IdentityT

flift :: (Functor s, FStrong mm, Functor x)
  => mm x ~> StateT s mm x
flift mm = AdjointT $ Curried \sf -> fstrength' (day sf mm)

toOuter :: (Functor x, FFunctor mm) => StateT ((,) s0) mm x ~> Simple.Outer.StateT s0 mm x
toOuter = AdjointT . ffmap (ffmap dayToEnv) . curriedToReader . runAdjointT

fromOuter :: (Functor x, FFunctor mm) => Simple.Outer.StateT s0 mm x ~> StateT ((,) s0) mm x
fromOuter = AdjointT . ffmap (ffmap envToDay) . readerToCurried . runAdjointT

toInner :: (Functor x, FFunctor mm) => StateT ((->) s1) mm x ~> Simple.Inner.StateT s1 mm x
toInner = AdjointT . ffmap (ffmap dayToTraced) . curriedToWriter . runAdjointT

fromInner :: (Functor x, FFunctor mm) => Simple.Inner.StateT s1 mm x ~> StateT ((->) s1) mm x
fromInner = AdjointT . ffmap (ffmap tracedToDay) . writerToCurried . runAdjointT
