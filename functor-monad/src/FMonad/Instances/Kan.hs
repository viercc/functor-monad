{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module FMonad.Instances.Kan() where

import Control.Comonad (Comonad (..), (=>=))
import Data.Functor.Kan.Lan
import Data.Functor.Kan.Ran

import {-# SOURCE #-} FMonad
import FFunctor.Instances.Kan()

-- | @Ran w (Ran w f) ~ Ran ('Compose' w w) f@
instance (Comonad w) => FMonad (Ran w) where
  fpure ::
    forall f x.
    (Functor f) =>
    f x ->
    Ran w f x
  --       f x -> (forall b. (x -> w b) -> f b)
  fpure f = Ran $ \k -> fmap (extract . k) f

  fbind :: (Functor g, Functor h) =>
     (g ~> Ran w h) -> (Ran w g ~> Ran w h)
  fbind k wg = Ran $ \xd -> runRan (k (runRan wg (duplicate . xd))) id

-- | @Lan w (Lan w f) ~ Lan ('Compose' w w) f@
instance (Comonad w) => FMonad (Lan w) where
  fpure ::
    forall f x.
    (Functor f) =>
    f x ->
    Lan w f x
  --       f x -> exists b. (w b -> x, f b)
  fpure f = Lan extract f
  
  fbind :: (Functor g, Functor h) =>
    (g ~> Lan w h) -> (Lan w g ~> Lan w h)
  fbind k (Lan j1 g) = case k g of
    Lan j2 h -> Lan (j2 =>= j1) h
