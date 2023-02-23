{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module FComonad
  ( type (~>),
    FFunctor (..),
    FComonad (..)
  ) where

import Data.Functor.Product

import Control.Monad.Trans.Identity

import FFunctor
import Data.Coerce (coerce)

class FComonad ff where
    fextract :: Functor g => ff g ~> g
    fduplicate :: Functor g => ff g ~> ff (ff g)

instance FComonad IdentityT where
    fextract = coerce
    fduplicate = coerce

instance Functor f => FComonad (Product f) where
    fextract (Pair _ g) = g
    fduplicate (Pair f g) = Pair f (Pair f g)

