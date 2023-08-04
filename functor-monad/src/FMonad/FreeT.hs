{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module FMonad.FreeT
  ( module FMonad,
    FreeT (..),
    FreeT' (..),
  )
where

import Control.Applicative (Alternative)
import Control.Monad (MonadPlus)
import Control.Monad.Trans.Free hiding (FreeT ())
import qualified Control.Monad.Trans.Free as Original
import Control.Monad.Trans.Free.Extra
import Data.Functor.Classes
import FMonad

-- | Redefine FreeT so that some instances don't require 'Monad' instead of 'Functor'
newtype FreeT f m b = WrapFreeT {unwrapFreeT :: Original.FreeT f m b}
  deriving
    ( Applicative,
      Alternative,
      Monad,
      MonadPlus,
      Foldable,
      Eq1,
      Ord1,
      Show1,
      Read1
    )
    via (Original.FreeT f m)
  deriving
    (Show, Read, Eq, Ord)
    via (Original.FreeT f m b)

newtype FreeT' m f b = WrapFreeT' {unwrapFreeT' :: Original.FreeT f m b}
  deriving
    (Functor)
    via (FreeT f m)
  deriving
    ( Applicative,
      Alternative,
      Monad,
      MonadPlus,
      Foldable,
      Eq1,
      Ord1,
      Show1,
      Read1
    )
    via (Original.FreeT f m)
  deriving
    (Show, Read, Eq, Ord)
    via (Original.FreeT f m b)

instance (Functor m, Functor f) => Functor (FreeT m f) where
  fmap f = WrapFreeT . fmapFreeT_ f . unwrapFreeT

instance (Traversable f, Traversable m) => Traversable (FreeT f m) where
  traverse f (WrapFreeT mx) = WrapFreeT <$> traverseFreeT_ f mx

instance (Traversable f, Traversable m) => Traversable (FreeT' f m) where
  traverse f (WrapFreeT' mx) = WrapFreeT' <$> traverseFreeT_ f mx

instance Functor f => FFunctor (FreeT f) where
  ffmap f = WrapFreeT . hoistFreeT f . unwrapFreeT

instance Functor f => FMonad (FreeT f) where
  fpure = WrapFreeT . inr
  fbind m k = WrapFreeT . fconcatFreeT_ . hoistFreeT unwrapFreeT . unwrapFreeT $ ffmap k m

instance Functor m => FFunctor (FreeT' m) where
  ffmap f = WrapFreeT' . transFreeT_ f . unwrapFreeT'

instance Monad m => FMonad (FreeT' m) where
  fpure :: forall g. Functor g => g ~> FreeT' m g
  fpure = WrapFreeT' . inl

  fbind :: forall g h a. (Monad m, Functor g, Functor h) => FreeT' m g a -> (g ~> FreeT' m h) -> FreeT' m h a
  fbind m k = WrapFreeT' . eitherFreeT_ id inr . transFreeT_ unwrapFreeT' . unwrapFreeT' $ ffmap k m
