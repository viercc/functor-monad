{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
module FMonad.Adjoint(Adjoint(..), AdjointT(..), toAdjointT, fromAdjointT) where

import Control.Monad.Trans.Identity ( IdentityT(runIdentityT) )

import FFunctor
import FMonad
import FStrong
import FFunctor.FCompose
import FFunctor.Adjunction

type Adjoint :: FF -> FF -> FF
newtype Adjoint ff uu g x = Adjoint { runAdjoint :: uu (ff g) x }
    deriving Functor

deriving
  via FCompose uu ff
    instance (FFunctor ff, FFunctor uu) => FFunctor (Adjoint ff uu)

deriving
  via FCompose uu ff
    instance (FStrong ff, FStrong uu) => FStrong (Adjoint ff uu)

instance (Adjunction ff uu) => FMonad (Adjoint ff uu) where
    fpure = Adjoint . unit
    fjoin = Adjoint . ffmap counit . runAdjoint . ffmap runAdjoint

newtype AdjointT ff uu mm g x = AdjointT { runAdjointT :: uu (mm (ff g)) x }
  deriving Functor

deriving
  via FCompose (FCompose uu mm) ff
    instance (FFunctor ff, FFunctor mm, FFunctor uu) => FFunctor (AdjointT ff uu mm)

deriving
  via FCompose (FCompose uu mm) ff
    instance (FStrong ff, FStrong mm, FStrong uu) => FStrong (AdjointT ff uu mm)

instance (Adjunction ff uu, FMonad mm) => FMonad (AdjointT ff uu mm) where
    fpure = AdjointT . ffmap fpure . unit
    fjoin = AdjointT . ffmap (fjoin . ffmap counit) . runAdjointT . ffmap runAdjointT

toAdjointT :: (FFunctor ff, FFunctor uu, FMonad mm, Functor g) => Adjoint ff uu g ~> AdjointT ff uu mm g
toAdjointT = AdjointT . ffmap fpure . runAdjoint

fromAdjointT :: (FFunctor ff, FFunctor uu, Functor g) => AdjointT ff uu IdentityT g ~> Adjoint ff uu g
fromAdjointT = Adjoint . ffmap runIdentityT . runAdjointT