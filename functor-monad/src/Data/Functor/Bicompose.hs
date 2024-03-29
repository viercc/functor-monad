{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
module Data.Functor.Bicompose where

import Control.Applicative (Alternative)
import Control.Monad (join)
import Data.Functor.Classes (Eq1, Ord1)
import Data.Functor.Compose
import Data.Kind (Type)
import FMonad
import FComonad

import Data.Functor.Precompose (type (:.:))
import Control.Comonad

-- | Both-side composition of Monad.
--
-- If both of @f@ and @g@ are @Monad@, @Bicompose f g@ is an instance of 'FMonad' in a similar way
-- 'Compose' and 'Data.Functor.Precompose.Precompose' are.
type Bicompose :: (k2 -> Type) -> (k0 -> k1) -> (k1 -> k2) -> k0 -> Type
newtype Bicompose f g h a = Bicompose {getBicompose :: f (h (g a))}
  deriving stock (Show, Read, Functor, Foldable)

deriving stock instance
  (Traversable f, Traversable g, Traversable h) => Traversable (Bicompose f g h)

deriving via
  ((f :.: h :.: g) a)
  instance
    (Eq1 f, Eq1 g, Eq1 h, Eq a) => Eq (Bicompose f g h a)

deriving via
  ((f :.: h :.: g) a)
  instance
    (Ord1 f, Ord1 g, Ord1 h, Ord a) => Ord (Bicompose f g h a)

deriving via
  (f :.: h :.: g)
  instance
    (Applicative f, Applicative g, Applicative h) => Applicative (Bicompose f g h)

deriving via
  (f :.: h :.: g)
  instance
    (Alternative f, Applicative g, Applicative h) => Alternative (Bicompose f g h)

instance (Functor f, Functor g) => FFunctor (Bicompose f g) where
  ffmap gh = Bicompose . fmap gh . getBicompose

instance (Monad f, Monad g) => FMonad (Bicompose f g) where
  fpure = Bicompose . return . fmap return
  fbind k = Bicompose . fmap (fmap join) . (getBicompose . k =<<) . getBicompose

instance (Comonad f, Comonad g) => FComonad (Bicompose f g) where
  fextract = fmap extract . extract . getBicompose
  fextend tr = Bicompose . extend (tr . Bicompose) . fmap (fmap duplicate) . getBicompose