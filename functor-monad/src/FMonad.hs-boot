{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module FMonad
  ( type (~>),
    FFunctor (..),
    FMonad (..),
    fjoin
  )
where

import {-# SOURCE #-} FFunctor

import Data.Functor.Compose ( Compose )
import Data.Functor.Product ( Product )
import Data.Functor.Sum ( Sum )
import Data.Functor.Precompose (Precompose)
import Data.Functor.Bicompose (Bicompose)

class FFunctor ff => FMonad ff where
  fpure :: (Functor g) => g ~> ff g
  fbind :: (Functor g, Functor h) => (g ~> ff h) -> ff g a -> ff h a

fjoin :: (FMonad ff, Functor g) => ff (ff g) ~> ff g

instance Functor f => FMonad (Sum f)
instance (Functor f, forall a. Monoid (f a)) => FMonad (Product f)
instance Monad f => FMonad (Compose f)
instance Monad f => FMonad (Precompose f)
instance (Monad f, Monad g) => FMonad (Bicompose f g)