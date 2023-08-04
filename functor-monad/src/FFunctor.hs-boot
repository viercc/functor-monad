{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module FFunctor
  ( type (~>),
    FUNCTOR,
    FF,
    FFunctor (..),
  )
where

import Data.Kind

import Data.Functor.Compose ( Compose )
import Data.Functor.Product ( Product )
import Data.Functor.Sum ( Sum )

-- | Natural transformation arrow
type (~>) :: (k -> Type) -> (k -> Type) -> Type
type (~>) f g = forall x. f x -> g x

-- | The kind of a @Functor@
type FUNCTOR = Type -> Type

-- | The kind of a @FFunctor@.
type FF = FUNCTOR -> FUNCTOR

type FFunctor :: FF -> Constraint
class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
  ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g x -> ff h x)

instance Functor f => FFunctor (Sum f)
instance Functor f => FFunctor (Product f)
instance Functor f => FFunctor (Compose f)