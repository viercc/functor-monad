{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Data.Functor.Precompose where

import Data.Kind (Type)

import Control.Applicative (Alternative)
import Control.Monad (join)
import Control.Comonad(Comonad(..))
import Data.Functor.Classes (Eq1, Ord1)
import Data.Functor.Compose ( Compose(..) )

import FMonad
import FComonad

-- | Single-kinded type alias of Compose
type (:.:) :: (Type -> Type) -> (Type -> Type) -> Type -> Type
type (:.:) = Compose

-- | Flipped-order Compose.
--
-- When @f@ is a @Monad@, @Precompose f@ is a 'FMonad' in the similar way 'Compose' is.
--
-- The only difference is @Precompose f@ composes @f@ to the right (_pre_compose)
-- compared to @Compose f@ which composes to the left (_post_compose).
type Precompose :: (j -> k) -> (k -> Type) -> j -> Type
newtype Precompose f g a = Precompose {getPrecompose :: g (f a)}
  deriving stock (Show, Read, Functor, Foldable)

deriving stock instance (Traversable f, Traversable g) => Traversable (Precompose f g)

deriving via
  ((g :.: f) a)
  instance
    (Eq1 f, Eq1 g, Eq a) => Eq (Precompose f g a)

deriving via
  ((g :.: f) a)
  instance
    (Ord1 f, Ord1 g, Ord a) => Ord (Precompose f g a)

deriving via
  (g :.: f)
  instance
    (Eq1 f, Eq1 g) => Eq1 (Precompose f g)

deriving via
  (g :.: f)
  instance
    (Ord1 f, Ord1 g) => Ord1 (Precompose f g)

deriving via
  (g :.: f)
  instance
    (Applicative f, Applicative g) => Applicative (Precompose f g)

deriving via
  (g :.: f)
  instance
    (Applicative f, Alternative g) => Alternative (Precompose f g)

instance Functor f => FFunctor (Precompose f) where
  ffmap gh = Precompose . gh . getPrecompose

instance Monad f => FMonad (Precompose f) where
  fpure = Precompose . fmap return
  fbind k = Precompose . fmap join . getPrecompose . k . getPrecompose

instance Comonad f => FComonad (Precompose f) where
  fextract = fmap extract . getPrecompose
  fextend tr = Precompose . tr . Precompose . fmap duplicate . getPrecompose