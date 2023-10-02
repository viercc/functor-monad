{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
module FMonad.Adjoint(Adjoint, adjoint, runAdjoint, AdjointT(..), fffmap, generalize) where

import Control.Monad.Trans.Identity ( IdentityT(..) )

import FFunctor
import FMonad
import FStrong
import FFunctor.FCompose
import FFunctor.Adjunction

newtype AdjointT ff uu mm g x = AdjointT { runAdjointT :: uu (mm (ff g)) x }

type Adjoint ff uu = AdjointT ff uu IdentityT

deriving
  via FCompose (FCompose uu mm) ff g
    instance (FFunctor ff, FFunctor mm, FFunctor uu, Functor g) => Functor (AdjointT ff uu mm g)

deriving
  via FCompose (FCompose uu mm) ff
    instance (FFunctor ff, FFunctor mm, FFunctor uu) => FFunctor (AdjointT ff uu mm)

deriving
  via FCompose (FCompose uu mm) ff
    instance (FStrong ff, FStrong mm, FStrong uu) => FStrong (AdjointT ff uu mm)

instance (Adjunction ff uu, FMonad mm) => FMonad (AdjointT ff uu mm) where
    fpure = AdjointT . ffmap fpure . unit
    fbind k = AdjointT . ffmap (fbind counit) . runAdjointT . ffmap (runAdjointT . k)

adjoint :: (FFunctor ff, FFunctor uu, Functor x) => uu (ff x) ~> Adjoint ff uu x
adjoint = AdjointT . ffmap IdentityT

runAdjoint :: (FFunctor ff, FFunctor uu, Functor x) => Adjoint ff uu x ~> uu (ff x)
runAdjoint = ffmap runIdentityT . runAdjointT

fffmap :: forall mm nn ff uu x.
     (FFunctor mm, FFunctor nn, FFunctor ff, FFunctor uu, Functor x)
  => (forall y. (Functor y) => mm y ~> nn y)
  -> (AdjointT ff uu mm x ~> AdjointT ff uu nn x)
fffmap trans = AdjointT . ffmap trans . runAdjointT

generalize :: (FMonad mm, FFunctor ff, FFunctor uu, Functor x) => Adjoint ff uu x ~> AdjointT ff uu mm x
generalize = fffmap (fpure . runIdentityT)
