{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}

module FMonad.State.Day
  (StateT(..),
   flift,
   toOuter, fromOuter, toInner, fromInner,
   
   State, state, state_, get, put,
   runState
) where

import Control.Monad.Trans.Identity
import Data.Functor.Day ( Day(..), day )
import Data.Functor.Day.Curried ( Curried(Curried) )
import Data.Functor.Day.Comonoid

import FMonad
import FMonad.Adjoint
import FStrong

import qualified FMonad.State.Simple.Inner as Simple.Inner
import qualified FMonad.State.Simple.Outer as Simple.Outer

import Data.Functor.Day.Extra
import Data.Coerce (coerce)
import Data.Functor.Identity
import Data.Function ((&))

newtype StateT s mm x a = StateT { runStateT :: forall r. s (a -> r) -> mm (Day s x) r }
   deriving stock Functor
   deriving (FFunctor, FMonad) via (AdjointT (Day s) (Curried s) mm)

toAdjointT :: StateT s mm x ~> AdjointT (Day s) (Curried s) mm x
toAdjointT = coerce

fromAdjointT :: AdjointT (Day s) (Curried s) mm x ~> StateT s mm x
fromAdjointT = coerce

flift :: (Functor s, FStrong mm, Functor x)
  => mm x ~> StateT s mm x
flift mm = StateT $ \sf -> fstrength' (day sf mm)

toOuter :: (Functor x, FFunctor mm) => StateT ((,) s0) mm x ~> Simple.Outer.StateT s0 mm x
toOuter = Simple.Outer.fromAdjointT . AdjointT . ffmap (ffmap dayToEnv) . curriedToReader . runAdjointT . toAdjointT

fromOuter :: (Functor x, FFunctor mm) => Simple.Outer.StateT s0 mm x ~> StateT ((,) s0) mm x
fromOuter = fromAdjointT . AdjointT . ffmap (ffmap envToDay) . readerToCurried . runAdjointT . Simple.Outer.toAdjointT

toInner :: (Functor x, FFunctor mm) => StateT ((->) s1) mm x ~> Simple.Inner.StateT s1 mm x
toInner = Simple.Inner.fromAdjointT . AdjointT . ffmap (ffmap dayToTraced) . curriedToWriter . runAdjointT . toAdjointT

fromInner :: (Functor x, FFunctor mm) => Simple.Inner.StateT s1 mm x ~> StateT ((->) s1) mm x
fromInner = fromAdjointT . AdjointT . ffmap (ffmap tracedToDay) . writerToCurried . runAdjointT . Simple.Inner.toAdjointT

type State s = StateT s IdentityT

state :: (FMonad mm)
  => (forall r. s (a -> r) -> Day s x r)
  -> StateT s mm x a
state f = StateT $ \sar -> fpure (f sar)

state_ :: (Functor s, FMonad mm)
  => (forall b. s b -> (s b, x a))
  -> StateT s mm x a
state_ f = state (uncurry day . f)

get :: (Comonoid s, FMonad mm) => StateT s mm s ()
get = state (fmap ($ ()) . coapply)

put :: (Comonad s, FMonad mm) => s a -> StateT s mm Identity a
put sa = state (\sar -> Day sa (Identity (extract sar)) (&))

runState :: State s x a -> s (a -> r) -> Day s x r
runState sx = runIdentityT . runStateT sx
