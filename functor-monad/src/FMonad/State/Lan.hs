{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
module FMonad.State.Lan
  (StateT(..),
   fromAdjointT,
   toAdjointT,
   toInner, fromInner,
   
   State,
   state, runState
  ) where

import Control.Monad.Trans.Identity
import Data.Functor.Kan.Lan
import Data.Functor.Precompose
import qualified FMonad.State.Simple.Inner as Simple.Inner

import FMonad
import FMonad.Adjoint
import Data.Tuple (swap)
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Comonad.Traced (TracedT(..))
import Data.Coerce (coerce)

-- type StateT s = AdjointT (Lan s) (Precompose s)
newtype StateT s mm x a = StateT { runStateT :: mm (Lan s x) (s a) }
  deriving (FFunctor, FMonad) via (AdjointT (Lan s) (Precompose s) mm)

deriving
  stock instance (FFunctor mm, Functor s) => Functor (StateT s mm x)

toAdjointT :: StateT s mm x ~> AdjointT (Lan s) (Precompose s) mm x
toAdjointT = coerce

fromAdjointT :: AdjointT (Lan s) (Precompose s) mm x ~> StateT s mm x
fromAdjointT = coerce

toInner :: (Functor x, FFunctor mm) => StateT ((,) s1) mm x ~> Simple.Inner.StateT s1 mm x
toInner = Simple.Inner.fromAdjointT . AdjointT . ffmap (ffmap lanToTraced) . (WriterT . fmap swap . getPrecompose) . runAdjointT . toAdjointT

fromInner :: (Functor x, FFunctor mm) => Simple.Inner.StateT s1 mm x ~> StateT ((,) s1) mm x
fromInner = fromAdjointT . AdjointT . ffmap (ffmap tracedToLan) . (Precompose . fmap swap . runWriterT) . runAdjointT . Simple.Inner.toAdjointT

lanToTraced :: Functor f => Lan ((,) s1) f ~> TracedT s1 f
lanToTraced (Lan sr_a fr) = TracedT $ fmap (\r s -> sr_a (s,r)) fr

tracedToLan :: TracedT s1 f ~> Lan ((,) s1) f
tracedToLan (TracedT fsa) = Lan (\(s1,sa) -> sa s1) fsa

-- * Pure state

type State s = StateT s IdentityT

state :: (Functor s, FMonad mm, Functor x)
  => (s b -> s a) -> x b -> StateT s mm x a
state f xb = StateT $ fpure (Lan f xb)

runState :: State s x a -> Lan s x (s a)
runState = runIdentityT . runStateT
