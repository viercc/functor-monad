{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Functor.Flip1 where

import AutoLift (Reflected1 (..))
import Control.Applicative
import Control.Monad
import Control.Monad.Free (MonadFree (..))
import Data.Coerce
import Data.Functor.Classes
import Data.Kind (Type)

type Flip1 :: (k1 -> k2 -> Type -> Type) -> k2 -> k1 -> Type -> Type
newtype Flip1 t f g x = Flip1 {unFlip1 :: t g f x}
  deriving stock (Eq, Ord, Show, Read, Traversable)
  deriving
    ( Functor,
      Foldable,
      Applicative,
      Alternative,
      Monad,
      MonadPlus,
      MonadFail
    )
    via (t g f)
  deriving (Eq1, Ord1) via (t g f)

deriving via
  (Reflected1 (Flip1 t f g))
  instance
    ( forall a. Show a => Show (t g f a),
      forall x y. Coercible x y => Coercible (t g f x) (t g f y)
    ) =>
    Show1 (Flip1 t f g)

deriving via
  (Reflected1 (Flip1 t f g))
  instance
    ( forall a. Read a => Read (t g f a),
      forall x y. Coercible x y => Coercible (t g f x) (t g f y)
    ) =>
    Read1 (Flip1 t f g)

instance (Functor h, MonadFree h (t g f)) => MonadFree h (Flip1 t f g) where
  wrap = Flip1 . wrap . fmap unFlip1
