{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
module FMonad.FFree where

import Data.Functor.Identity

import FFunctor
import FStrong
import FMonad

import Data.Functor.Day ( Day(..) )

data FFree ff g x = FPure (g x) | FFree (ff (FFree ff g) x)

deriving instance (Show (g a), Show (ff (FFree ff g) a)) => Show (FFree ff g a)
deriving instance (Eq (g a), Eq (ff (FFree ff g) a)) => Eq (FFree ff g a)
deriving instance (Ord (g a), Ord (ff (FFree ff g) a)) => Ord (FFree ff g a)
deriving instance (Functor g, Functor (ff (FFree ff g))) => Functor (FFree ff g)
deriving instance (Foldable g, Foldable (ff (FFree ff g))) => Foldable (FFree ff g)
deriving instance (Traversable g, Traversable (ff (FFree ff g))) => Traversable (FFree ff g)

instance (FFunctor ff) => FFunctor (FFree ff) where 
    ffmap gh (FPure gx) = FPure (gh gx)
    ffmap gh (FFree fmx) = FFree (ffmap (ffmap gh) fmx)

instance (FFunctor ff) => FMonad (FFree ff) where
    fpure = FPure
    fjoin (FPure mx) = mx
    fjoin (FFree fmmx) = FFree (ffmap fjoin fmmx)

instance (FStrong ff) => FStrong (FFree ff) where
    fstrength (Day ffg h op) = case ffg of
      FPure g -> FPure (Day g h op)
      FFree ffr -> FFree (ffmap fstrength $ fstrength (Day ffr h op))

iter :: forall ff g. (FFunctor ff, Functor g) => (ff g ~> g) -> FFree ff g ~> g
iter step = go
  where
    go :: FFree ff g ~> g
    go (FPure gx) = gx
    go (FFree fmx) = step (ffmap go fmx)

foldFFree :: forall ff mm g. (FFunctor ff, FMonad mm, Functor g) => (forall h. Functor h => ff h ~> mm h) -> FFree ff g ~> mm g
foldFFree toMM = go
  where
    go :: FFree ff g ~> mm g
    go (FPure gx) = fpure gx
    go (FFree ftx) = fjoin (ffmap go (toMM ftx))

retract :: (FMonad ff, Functor g) => FFree ff g ~> ff g
retract = foldFFree id

instance FStrong ff => Applicative (FFree ff Identity) where
    pure = FPure . Identity
    FPure (Identity x) <*> y = x <$> y
    FFree ffr <*> y = FFree $ innerAp ffr y

liftF :: (FFunctor ff, Functor g) => ff g ~> FFree ff g
liftF fgx = FFree (ffmap FPure fgx)
