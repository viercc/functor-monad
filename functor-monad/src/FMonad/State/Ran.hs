{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module FMonad.State.Ran
  (StateT, State, toInner, fromInner, generalize) where

import Control.Monad.Trans.Identity
import Data.Functor.Kan.Ran
import Data.Functor.Precompose
import qualified FMonad.State.Simple.Inner as Simple.Inner

import FMonad
import FMonad.Adjoint
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Comonad.Traced (TracedT(..))

type StateT s = AdjointT (Precompose s) (Ran s)
type State s = StateT s IdentityT

toInner :: (Functor x, FFunctor mm) => StateT ((->) s1) mm x ~> Simple.Inner.StateT s1 mm x
toInner = AdjointT . ffmap (ffmap (TracedT . getPrecompose)) . ranToWriter . runAdjointT

fromInner :: (Functor x, FFunctor mm) => Simple.Inner.StateT s1 mm x ~> StateT ((->) s1) mm x
fromInner = AdjointT . ffmap (ffmap (Precompose . runTracedT)) . writerToRan . runAdjointT

ranToWriter :: Functor f => Ran ((->) s1) f ~> WriterT s1 f
ranToWriter (Ran ran) = WriterT $ ran (,)

writerToRan :: Functor f => WriterT s1 f ~> Ran ((->) s1) f
writerToRan (WriterT f_as) = Ran $ \k -> fmap (uncurry k) f_as