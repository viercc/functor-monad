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

-- | 'Original.FreeT' is a 'FMonad' in two different ways
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

-- | @FreeT f@ is 'FMonad' for any @Functor f@.
--   
--   Due to a historical reason, the original 'Original.FreeT' type requires @Monad m@
--   to be a @Functor@ itself (in other words, to have @Functor (FreeT f m)@ instance.)
--   That blocks @FreeT f@ becomes a @FFunctor@. The @FreeT@ type this module exports is
--   a thin wrapper around the original, \"fix\"ing its @Functor@ instance.
--   
-- @
-- import Control.Monad.Trans.Free as Original
-- 
-- instance (Functor f, Monad m)   => Functor (Original.FreeT f m)
-- instance (Functor f, Functor m) => Functor (FreeT f m)
-- instance (Functor f) => FFunctor (FreeT f)
-- @
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

-- | @FreeT'@ is a @FreeT@ but its arguments are flipped.
--
-- @
-- FreeT' m f a ≡ FreeT f m a
-- @
--   
-- @FreeT' m@ is a @FFunctor@ and @FMonad@ evidenced by these existing functions,
-- specialized for the purpose.
--   
-- @
-- 'Original.transFreeT' :: (Functor g, Functor m) => (f ~> g) -> FreeT f m ~> FreeT g m
-- 'Original.liftF' :: (Functor f, Monad m) => f ~> FreeT f m
-- 'Original.foldFreeT' id :: (Functor f, Monad m) => FreeT (FreeT f m) m ~> FreeT f m 
-- @
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
  fbind k = WrapFreeT . fconcatFreeT_ . hoistFreeT unwrapFreeT . unwrapFreeT . ffmap k

instance Functor m => FFunctor (FreeT' m) where
  ffmap f = WrapFreeT' . transFreeT_ f . unwrapFreeT'

instance Monad m => FMonad (FreeT' m) where
  fpure :: forall g. Functor g => g ~> FreeT' m g
  fpure = WrapFreeT' . inl

  fbind :: forall g h a. (Functor g, Functor h) => (g ~> FreeT' m h) -> FreeT' m g a -> FreeT' m h a
  fbind k = WrapFreeT' . eitherFreeT_ id inr . transFreeT_ unwrapFreeT' . unwrapFreeT' . ffmap k
