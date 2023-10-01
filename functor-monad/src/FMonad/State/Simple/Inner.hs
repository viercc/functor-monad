{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

module FMonad.State.Simple.Inner
  (StateT(..),
   flift,
   toAdjointT,
   fromAdjointT,
   
   State,
   state,
   runState
) where

import Control.Monad.Trans.Identity ( IdentityT(..) )
import Control.Comonad.Trans.Traced ( TracedT(..) )
import Control.Monad.Trans.Writer ( WriterT(..) )
import Data.Functor.Day (Day(..), swapped)
import Data.Functor.Day.Extra (dayToTraced)
import Data.Coerce (coerce)

import FMonad
import FMonad.Adjoint
import FStrong

newtype StateT s1 mm x a = StateT { runStateT :: mm (TracedT s1 x) (a, s1) }
   deriving (FFunctor, FMonad) via (AdjointT (TracedT s1) (WriterT s1) mm)
type State s1 = StateT s1 IdentityT

deriving
  stock instance (FFunctor mm, Functor x) => Functor (StateT s1 mm x)

toAdjointT :: StateT s1 mm x ~> AdjointT (TracedT s1) (WriterT s1) mm x
toAdjointT = coerce

fromAdjointT :: AdjointT (TracedT s1) (WriterT s1) mm x ~> StateT s1 mm x
fromAdjointT = coerce

flift :: (FStrong mm, Functor x)
  => mm x ~> StateT s1 mm x
flift mm = fromAdjointT $ AdjointT $ WriterT $ ffmap (dayToTraced . swapped) (fstrength (Day mm id (,)))

state :: forall s1 x mm a. (Functor x, FMonad mm) => x (s1 -> (a, s1)) -> StateT s1 mm x a
state = StateT . fpure . TracedT

runState :: State s1 x a -> x (s1 -> (a, s1))
runState = coerce
