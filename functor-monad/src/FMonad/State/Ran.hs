{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
module FMonad.State.Ran
  (StateT(..),
  toInner, fromInner,
  
  State, state, state_, get, put,
  runState
  ) where

import Control.Monad.Trans.Identity
import Data.Functor.Kan.Ran
import Data.Functor.Precompose
import Data.Coerce (coerce)
import Control.Comonad (Comonad(..))
import Data.Functor.Identity
import FMonad
import FMonad.Adjoint
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Comonad.Traced (TracedT(..))

import qualified FMonad.State.Simple.Inner as Simple.Inner

-- type StateT s = AdjointT (Precompose s) (Ran s)
newtype StateT s mm x a = StateT { runStateT :: forall r. (a -> s r) -> mm (Precompose s x) r }
  deriving (FFunctor, FMonad) via (AdjointT (Precompose s) (Ran s) mm)

deriving
  stock instance (FFunctor mm, Functor s) => Functor (StateT s mm x)

fromAdjointT :: AdjointT (Precompose s) (Ran s) mm x ~> StateT s mm x
fromAdjointT = coerce

toAdjointT :: StateT s mm x ~> AdjointT (Precompose s) (Ran s) mm x
toAdjointT = coerce

toInner :: (Functor x, FFunctor mm) => StateT ((->) s1) mm x ~> Simple.Inner.StateT s1 mm x
toInner = Simple.Inner.fromAdjointT . AdjointT . ffmap (ffmap (TracedT . getPrecompose)) . ranToWriter . runAdjointT . toAdjointT

fromInner :: (Functor x, FFunctor mm) => Simple.Inner.StateT s1 mm x ~> StateT ((->) s1) mm x
fromInner = fromAdjointT . AdjointT . ffmap (ffmap (Precompose . runTracedT)) . writerToRan . runAdjointT . Simple.Inner.toAdjointT

ranToWriter :: Functor f => Ran ((->) s1) f ~> WriterT s1 f
ranToWriter (Ran ran) = WriterT $ ran (,)

writerToRan :: Functor f => WriterT s1 f ~> Ran ((->) s1) f
writerToRan (WriterT f_as) = Ran $ \k -> fmap (uncurry k) f_as

-- * Pure state

type State s = StateT s IdentityT

state :: (Functor s, Functor x, FMonad mm)
  => (forall r. (a -> s r) -> x (s r))
  -> StateT s mm x a
state f = StateT $ \k -> fpure (Precompose (f k))

state_ :: (Functor s, Functor x, FMonad mm)
  => (forall r. s r -> x (s r))
  -> StateT s mm x ()
state_ f = state (\k -> f (k ()))

get :: (Comonad s, FMonad mm) => StateT s mm s ()
get = state_ duplicate

put :: (Comonad s, FMonad mm) => s a -> StateT s mm Identity a
put sa = state (\k -> Identity (extract . k <$> sa))

runState :: State s x a -> (a -> s r) -> x (s r)
runState sm k = getPrecompose $ runIdentityT $ runStateT sm k
