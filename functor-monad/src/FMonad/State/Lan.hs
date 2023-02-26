{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module FMonad.State.Lan
  (StateT, State, toInner, fromInner, generalize) where

import Control.Monad.Trans.Identity
import Data.Functor.Kan.Lan
import Data.Functor.Precompose
import qualified FMonad.State.Simple.Inner as Simple.Inner

import FMonad
import FMonad.Adjoint
import Data.Tuple (swap)
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Comonad.Traced (TracedT(..))

type StateT s = AdjointT (Lan s) (Precompose s)
type State s = StateT s IdentityT

toInner :: (Functor x, FFunctor mm) => StateT ((,) s1) mm x ~> Simple.Inner.StateT s1 mm x
toInner = AdjointT . ffmap (ffmap lanToTraced) . (WriterT . fmap swap . getPrecompose) . runAdjointT

fromInner :: (Functor x, FFunctor mm) => Simple.Inner.StateT s1 mm x ~> StateT ((,) s1) mm x
fromInner = AdjointT . ffmap (ffmap tracedToLan) . (Precompose . fmap swap . runWriterT) . runAdjointT

lanToTraced :: Functor f => Lan ((,) s1) f ~> TracedT s1 f
lanToTraced (Lan sr_a fr) = TracedT $ fmap (\r s -> sr_a (s,r)) fr

tracedToLan :: TracedT s1 f ~> Lan ((,) s1) f
tracedToLan (TracedT fsa) = Lan (\(s1,sa) -> sa s1) fsa