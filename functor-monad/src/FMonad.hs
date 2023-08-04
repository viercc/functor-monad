{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module FMonad
  ( type (~>),
    FFunctor (..),
    FMonad (..),
    fjoin
  )
where

import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Sum

import qualified Data.Bifunctor.Product as Bi
import qualified Data.Bifunctor.Product.Extra as Bi

import FFunctor

import FMonad.Instances.Day()
import FMonad.Instances.Kan()
import FMonad.Instances.Trans()
import FMonad.Instances.Free()

-- | Monad on 'Functor's.
--
-- FMonad laws:
--
-- [fpure is natural in g]
--
--    For all @Functor g@, @Functor h@, and @n :: g ~> h@,
--
--    > ffmap n . fpure = fpure . n
--
-- [fjoin is natural in g]
--
--    For all @Functor g@, @Functor h@, and @n :: g ~> h@,
--
--    > ffmap n . fjoin = fjoin . ffmap (ffmap n)
--
-- [Left unit]
--
--    > fjoin . fpure = id
--
-- [Right unit]
--
--    > fjoin . fmap fpure = id
--
-- [Associativity]
--
--    > fjoin . fjoin = fjoin . ffmap fjoin
class FFunctor ff => FMonad ff where
  fpure :: (Functor g) => g ~> ff g
  fbind :: (Functor g, Functor h) => (g ~> ff h) -> ff g a -> ff h a

fjoin :: (FMonad ff, Functor g) => ff (ff g) ~> ff g
fjoin = fbind id

instance Functor f => FMonad (Sum f) where
  fpure = InR

  fbind _ (InL fa) = InL fa
  fbind k (InR ga) = k ga

instance (Functor f, forall a. Monoid (f a)) => FMonad (Product f) where
  fpure = Pair mempty
  fbind k (Pair fa1 ga) = case k ga of
    (Pair fa2 ha) -> Pair (fa1 <> fa2) ha

instance Monad f => FMonad (Compose f) where
  fpure = Compose . return
  fbind k = Compose . (>>= (getCompose . k)) . getCompose

instance (FMonad ff, FMonad gg) => FMonad (Bi.Product ff gg) where
  fpure h = Bi.Pair (fpure h) (fpure h)
  fbind k (Bi.Pair ff gg) = Bi.Pair (fbind (Bi.proj1 . k) ff) (fbind (Bi.proj2 . k) gg)
