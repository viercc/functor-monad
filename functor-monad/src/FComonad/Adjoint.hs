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
module FComonad.Adjoint(Adjoint(..), AdjointT(..), toAdjointT, fromAdjointT) where

import Control.Monad.Trans.Identity ( IdentityT(..) )

import FFunctor
import FComonad
import FStrong
import FFunctor.FCompose
import FFunctor.Adjunction

type Adjoint :: FF -> FF -> FF
newtype Adjoint ff uu g x = Adjoint { runAdjoint :: ff (uu g) x }
    deriving Functor

deriving
  via FCompose ff uu
    instance (FFunctor ff, FFunctor uu) => FFunctor (Adjoint ff uu)

deriving
  via FCompose ff uu
    instance (FStrong ff, FStrong uu) => FStrong (Adjoint ff uu)

instance (Adjunction ff uu) => FComonad (Adjoint ff uu) where
    fextract = counit . runAdjoint
    fextend tr = ffmap (tr . Adjoint) . Adjoint . ffmap unit . runAdjoint

newtype AdjointT ff uu ww g x = AdjointT { runAdjointT :: ff (ww (uu g)) x }
  deriving Functor

deriving
  via FCompose (FCompose ff ww) uu
    instance (FFunctor ff, FFunctor ww, FFunctor uu) => FFunctor (AdjointT ff uu ww)

deriving
  via FCompose (FCompose ff ww) uu
    instance (FStrong ff, FStrong ww, FStrong uu) => FStrong (AdjointT ff uu ww)

instance (Adjunction ff uu, FComonad ww) => FComonad (AdjointT ff uu ww) where
    fextract = counit . ffmap fextract . runAdjointT
    fextend tr = ffmap (tr . AdjointT) . AdjointT . ffmap (fextend unit) . runAdjointT

fromAdjointT :: (FFunctor ff, FFunctor uu, FComonad ww, Functor g) => AdjointT ff uu ww g ~> Adjoint ff uu g
fromAdjointT = Adjoint . ffmap fextract . runAdjointT

toAdjointT :: (FFunctor ff, FFunctor uu, Functor g) => Adjoint ff uu g ~> AdjointT ff uu IdentityT g 
toAdjointT = AdjointT . ffmap IdentityT . runAdjoint