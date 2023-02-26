{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
module FComonad.Adjoint(Adjoint, adjoint, runAdjoint, AdjointT(..), fffmap, ungeneralize) where

import Control.Monad.Trans.Identity ( IdentityT(..) )

import FFunctor
import FComonad
import FStrong
import FFunctor.FCompose
import FFunctor.Adjunction

newtype AdjointT ff uu ww g x = AdjointT { runAdjointT :: ff (ww (uu g)) x }
  deriving Functor

type Adjoint ff uu = AdjointT ff uu IdentityT

deriving
  via FCompose (FCompose ff ww) uu
    instance (FFunctor ff, FFunctor ww, FFunctor uu) => FFunctor (AdjointT ff uu ww)

deriving
  via FCompose (FCompose ff ww) uu
    instance (FStrong ff, FStrong ww, FStrong uu) => FStrong (AdjointT ff uu ww)

instance (Adjunction ff uu, FComonad ww) => FComonad (AdjointT ff uu ww) where
    fextract = counit . ffmap fextract . runAdjointT
    fextend tr = ffmap (tr . AdjointT) . AdjointT . ffmap (fextend unit) . runAdjointT

adjoint :: (FFunctor ff, FFunctor uu, Functor x) => ff (uu x) ~> Adjoint ff uu x
adjoint = AdjointT . ffmap IdentityT

runAdjoint :: (FFunctor ff, FFunctor uu, Functor x) => Adjoint ff uu x ~> ff (uu x)
runAdjoint = ffmap runIdentityT . runAdjointT

fffmap :: forall mm nn ff uu x.
     (FFunctor mm, FFunctor nn, FFunctor ff, FFunctor uu, Functor x)
  => (forall y. (Functor y) => mm y ~> nn y)
  -> (AdjointT ff uu mm x ~> AdjointT ff uu nn x)
fffmap trans = AdjointT . ffmap trans . runAdjointT

ungeneralize :: (FComonad ww, FFunctor ff, FFunctor uu, Functor x) => AdjointT ff uu ww x ~> Adjoint ff uu x
ungeneralize = fffmap (IdentityT . fextract)
