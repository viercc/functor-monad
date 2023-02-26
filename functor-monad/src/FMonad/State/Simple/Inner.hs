{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}

module FMonad.State.Simple.Inner
  (StateT, State, generalize,
   state, runState, flift) where

import Control.Monad.Trans.Identity ( IdentityT(..) )
import Control.Comonad.Trans.Traced ( TracedT(..) )
import Control.Monad.Trans.Writer ( WriterT(..) )
import Data.Functor.Day (Day(..), swapped)
import Data.Functor.Day.Extra (dayToTraced)
import Data.Coerce (coerce)

import FFunctor ( FFunctor(..), type (~>) )
import FMonad.Adjoint
import FStrong

type StateT s1 = AdjointT (TracedT s1) (WriterT s1)
type State s1 = StateT s1 IdentityT

flift :: (FStrong mm, Functor x)
  => mm x ~> StateT s1 mm x
flift mm = AdjointT $ WriterT $ ffmap (dayToTraced . swapped) (fstrength (Day mm id (,)))

state :: forall s1 x a. Functor x => x (s1 -> (a, s1)) -> State s1 x a
state = coerce

runState :: State s1 x a -> x (s1 -> (a, s1))
runState = coerce
