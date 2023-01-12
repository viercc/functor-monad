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

-- | Swaps the order of parameters. 'Flip1' is like 'Data.Bifunctor.Flip.Flip' but has
--   an additional parameter.
--
-- > newtype Flip1 t a b c = Flip1 {unFlip1 :: t b a c}
type Flip1 :: (k1 -> k2 -> k3 -> Type) -> k2 -> k1 -> k3 -> Type
newtype Flip1 t a b c = Flip1 {unFlip1 :: t b a c}
  deriving stock (Eq, Ord, Show, Read, Traversable)
  deriving
    ( Functor,
      Eq1,
      Ord1,
      Foldable,
      Applicative,
      Alternative,
      Monad,
      MonadPlus,
      MonadFail
    )
    via (t b a)

deriving via
  (Reflected1 (Flip1 t a b))
  instance
    ( forall c. Show c => Show (t b a c),
      forall x y. Coercible x y => Coercible (t b a x) (t b a y)
    ) =>
    Show1 (Flip1 t a b)

deriving via
  (Reflected1 (Flip1 t a b))
  instance
    ( forall c. Read c => Read (t b a c),
      forall x y. Coercible x y => Coercible (t b a x) (t b a y)
    ) =>
    Read1 (Flip1 t a b)

instance (Functor h, MonadFree h (t g f)) => MonadFree h (Flip1 t f g) where
  wrap = Flip1 . wrap . fmap unFlip1
