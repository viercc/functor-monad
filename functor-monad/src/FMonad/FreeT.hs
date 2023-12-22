{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Another way to make 'FreeT' an instance of 'FMonad'
-- 
-- 'FreeT' can be 'FMonad' in two different ways. There is already an instance:
-- 
-- @
-- instance Functor f => FMonad (FreeT f) where
--   fpure :: Functor m => m ~> FreeT f m
--   fbind :: (Functor m, Functor n) => (m ~> FreeT f n) -> (FreeT f m ~> FreeT f n)
-- @
-- 
-- In addition to this standard instance, @FreeT f m@ have @FMonad@-like structure by treating
-- @f@ as the parameter while fixing @m@ to some arbitrary @Monad@.
-- 
-- @
-- 'fpureFst' :: (Monad m) => (Functor f) => f ~> FreeT f m
-- 'fbindFst' :: (Monad m) => (Functor f, Functor g) => (f ~> FreeT g m) -> (FreeT f m ~> FreeT g m)
-- @
-- 
-- This module provides a newtype wrapper 'FreeT'' to use these as a real @FMonad@
-- instance.
module FMonad.FreeT
  ( FreeT' (..), liftM', fpureFst, fbindFst )
where

import Control.Applicative (Alternative)
import Control.Monad (MonadPlus)
import Control.Monad.Trans.Free
import Control.Monad.Trans.Free.Extra
import Data.Functor.Classes
import FMonad

-- | @FreeT'@ is a @FreeT@, but with the order of its arguments flipped.
--
-- @
-- FreeT' m f a ≡ FreeT f m a
-- @
newtype FreeT' m f b = WrapFreeT' {unwrapFreeT' :: FreeT f m b}
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
    via (FreeT f m)
  deriving
    (Show, Read, Eq, Ord)
    via (FreeT f m b)

-- | Lift of the Monad side.
liftM' :: Functor m => m a -> FreeT' m f a
liftM' = WrapFreeT' . inr

-- | @fpure@ to the first parameter of @FreeT@
fpureFst :: (Monad m) => (Functor f) => f ~> FreeT f m
fpureFst = liftF

-- | @fbind@ to the first parameter of @FreeT@
fbindFst :: (Monad m) => (Functor f, Functor g) => (f ~> FreeT g m) -> (FreeT f m ~> FreeT g m)
fbindFst k = eitherFreeT_ k inr

instance (Traversable f, Traversable m) => Traversable (FreeT' f m) where
  traverse f (WrapFreeT' mx) = WrapFreeT' <$> traverseFreeT_ f mx

instance Functor m => FFunctor (FreeT' m) where
  ffmap f = WrapFreeT' . transFreeT_ f . unwrapFreeT'

instance Monad m => FMonad (FreeT' m) where
  fpure :: forall g. Functor g => g ~> FreeT' m g
  fpure = WrapFreeT' . fpureFst

  fbind :: forall g h a. (Functor g, Functor h) => (g ~> FreeT' m h) -> FreeT' m g a -> FreeT' m h a
  fbind k = WrapFreeT' . fbindFst (unwrapFreeT' . k) . unwrapFreeT'
