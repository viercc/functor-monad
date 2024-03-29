{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Free 'FMonad'
module FMonad.FFree where

import Data.Functor.Day (Day (..), day, dap)
import FFunctor
import FMonad
import FStrong

-- | The free 'FMonad' for a @'FFunctor' ff@.  
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
  fbind k (FPure gx) = k gx
  fbind k (FFree fmmx) = FFree (ffmap (fbind k) fmmx)

instance (FStrong ff) => FStrong (FFree ff) where
  fstrength (Day ffg h op) = case ffg of
    FPure g -> FPure (Day g h op)
    FFree ffr -> FFree (ffmap fstrength $ fstrength (Day ffr h op))

fffmap :: forall ff gg h.
     (FFunctor ff, FFunctor gg, Functor h)
  => (forall h'. (Functor h') => ff h' ~> gg h')
  -> (FFree ff h ~> FFree gg h)
fffmap _ (FPure hx) = FPure hx
fffmap t (FFree ffm) = FFree $ ffmap (fffmap t) (t ffm)

-- | Iteratively fold a @FFree@ term down, given a way to fold one layer of @ff@. 
iter :: forall ff g. (FFunctor ff, Functor g) => (ff g ~> g) -> FFree ff g ~> g
iter step = go
  where
    go :: FFree ff g ~> g
    go (FPure gx) = gx
    go (FFree fmx) = step (ffmap go fmx)

-- | Fold a @FFree@ term to another @FMonad mm@.
foldFFree :: forall ff mm g. (FFunctor ff, FMonad mm, Functor g) => (forall h. Functor h => ff h ~> mm h) -> FFree ff g ~> mm g
foldFFree toMM = go
  where
    go :: FFree ff g ~> mm g
    go (FPure gx) = fpure gx
    go (FFree ftx) = fjoin (ffmap go (toMM ftx))

-- | @retract = 'foldFFree' id@
retract :: (FMonad ff, Functor g) => FFree ff g ~> ff g
retract = foldFFree id

instance (FStrong ff, Applicative g) => Applicative (FFree ff g) where
  pure = FPure . pure
  FPure gx <*> y = ffmap dap $ fstrength' (day gx y)
  FFree ffr <*> y = FFree $ innerAp ffr y

-- | Lift a single layer of @ff@ into @FFree ff@
liftF :: (FFunctor ff, Functor g) => ff g ~> FFree ff g
liftF fgx = FFree (ffmap FPure fgx)
