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

import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Sum
import Data.Kind (Constraint, Type)

import qualified Data.Bifunctor.Sum as Bi
import qualified Data.Bifunctor.Product as Bi

import FFunctor.Instances.Day()
import FFunctor.Instances.Kan()
import FFunctor.Instances.Trans()
import FFunctor.Instances.Free()
import Data.Functor.Precompose
import Data.Functor.Bicompose

-- | Natural transformation arrow
type (~>) :: (k -> Type) -> (k -> Type) -> Type
type (~>) f g = forall x. f x -> g x

-- | The kind of a @Functor@
type FUNCTOR = Type -> Type

-- | The kind of a @FFunctor@.
type FF = FUNCTOR -> FUNCTOR

-- | Endofunctors on the category of 'Functor's
--
-- FFunctor laws:
--
-- [Identity]
--
--    >  ffmap id = id
--
-- [Composition]
--
--    >  ffmap f . ffmap g = ffmap (f . g)
--
-- ==== Examples
--
-- @FFunctor@ instance of 'Sum' is defined as below:
--
-- > data Sum f g a = InL (f a) | InR (g a)
-- >
-- > instance (Functor f) => FFunctor (Sum f) where
-- >     ffmap :: (Functor g, Functor h) => (g ~> h) -> (Sum f g x -> Sum f h x)
-- >     ffmap gh fgx = case fgx of
-- >         InL fx -> InL fx
-- >         InR gx -> InR (gh gx)
--
-- Which can be said  @Functor (Either a)@ but each component is a @Functor@.
--
-- ==== @ContT@ is not an instance of @FFunctor@
--
-- @'Control.Monad.Trans.Cont.ContT' r@ has the kind matching to @FFunctor@, that is, taking a type constructor
-- @m :: Type -> Type@ and make @ContT r m :: Type -> Type@. But there can't be an instance @FFunctor (ContT r)@,
-- because @ContT r m@ uses @m@ in both positive and negative positions.
--
-- > newtype ContT r m a = ContT {
-- >     runContT :: (a -> m r) -> m r
-- >     --                ^       ^ positive position
-- >     --                | negative position
-- >   }
type FFunctor :: FF -> Constraint
class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
  ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g x -> ff h x)

instance Functor f => FFunctor (Sum f) where
  ffmap _ (InL fa) = InL fa
  ffmap gh (InR ga) = InR (gh ga)

instance Functor f => FFunctor (Product f) where
  ffmap gh (Pair fa ga) = Pair fa (gh ga)

instance Functor f => FFunctor (Compose f) where
  ffmap gh = Compose . fmap gh . getCompose

instance (FFunctor ff, FFunctor gg) => FFunctor (Bi.Sum ff gg) where
  ffmap t (Bi.L2 ff) = Bi.L2 (ffmap t ff)
  ffmap t (Bi.R2 gg) = Bi.R2 (ffmap t gg)

instance (FFunctor ff, FFunctor gg) => FFunctor (Bi.Product ff gg) where
  ffmap t (Bi.Pair ff gg) = Bi.Pair (ffmap t ff) (ffmap t gg)

instance Functor f => FFunctor (Precompose f) where
  ffmap gh = Precompose . gh . getPrecompose

instance (Functor f, Functor g) => FFunctor (Bicompose f g) where
  ffmap gh = Bicompose . fmap gh . getBicompose
