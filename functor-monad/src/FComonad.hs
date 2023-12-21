{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Comonads in the cateogory of @Functor@s.
module FComonad
  ( type (~>),
    FFunctor (..),
    FComonad (..),
    fduplicate
  ) where

import Control.Comonad

import Data.Functor.Product
import Data.Functor.Compose
import qualified Data.Bifunctor.Sum as Bi
import Control.Comonad.Trans.Identity
import Control.Comonad.Env ( EnvT(..) )
import Control.Comonad.Traced (TracedT(..))
import Control.Comonad.Cofree (Cofree(..))
import qualified Control.Comonad.Cofree as Cofree

import FFunctor
import Data.Coerce (coerce)

-- | @FComonad@ is to 'FFunctor' what 'Comonad' is to 'Functor'.
class FFunctor ff => FComonad ff where
    fextract :: Functor g => ff g ~> g
    fextend :: (Functor g, Functor h) => (ff g ~> h) -> (ff g ~> ff h)

fduplicate :: (FComonad ff, Functor g) => ff g ~> ff (ff g)
fduplicate = fextend id

instance FComonad IdentityT where
    fextract = coerce
    fextend tr = coerce . tr

instance Functor f => FComonad (Product f) where
    fextract (Pair _ g) = g
    fextend tr fg@(Pair f _) = Pair f (tr fg)

instance Comonad f => FComonad (Compose f) where
    fextract = extract . getCompose
    fextend tr = Compose . extend (tr . Compose) . getCompose

instance (FComonad ff, FComonad gg) => FComonad (Bi.Sum ff gg) where
    fextract (Bi.L2 ffx) = fextract ffx
    fextract (Bi.R2 ggx) = fextract ggx

    fextend tr ffgg = case ffgg of
      Bi.L2 ffx -> Bi.L2 (fextend (tr . Bi.L2) ffx)
      Bi.R2 ggx -> Bi.R2 (fextend (tr . Bi.R2) ggx)

instance FComonad (EnvT e) where
  fextract (EnvT _ gx) = gx
  fextend tr eg@(EnvT e _) = EnvT e (tr eg)

instance Monoid m => FComonad (TracedT m) where
  fextract (TracedT g) = ($ mempty) <$> g
  fextend tr (TracedT g) = TracedT $ tr (TracedT $ fmap (\k m1 m2 -> k (m1 <> m2)) g)

instance FComonad Cofree where
  fextract :: Functor g => Cofree g ~> g
  fextract = fmap extract . Cofree.unwrap

  fextend :: (Functor g, Functor h) => (Cofree g ~> h) -> (Cofree g ~> Cofree h)
  fextend tr = ffmap tr . Cofree.section

  {-
  
  fextract $ fduplicate gs
    = fextract $ extract gs :< fmap fduplicate_ (duplicate gs)
    = fmap extract (fmap fduplicate_ (duplicate gs))
    = fmap (extract . fduplicate_) (duplicate gs)
    = fmap extract (duplicate gs)
    = gs
  
  ffmap fextract $ fduplicate gs
    = ffmap fextract $ extract gs :< fmap fduplicate_ (duplicate gs)
    = extract gs :< (fmap (ffmap fextract) . fextract . fmap fduplicate_) (duplicate gs)
    = extract gs :< (fmap (ffmap fextract . fduplicate_) . fextract) (duplicate gs)
      -- gs = (a :< gs')
    = extract (a :< gs') :< fmap (ffmap fextract . fduplicate_) (fextract (duplicate (a :< gs')))
    = a :< fmap (ffmap fextract . fduplicate_) (fextract ((a :< gs') :< fmap duplicate gs'))
    = a :< fmap (ffmap fextract . fduplicate_) (fmap extract (fmap duplicate gs'))
    = a :< fmap (ffmap fextract . fduplicate_) gs'
  ffmap fextract . fduplicate_
    = let go (a :< gs) = a :< fmap go gs
       in go
    = id
  
  -}
