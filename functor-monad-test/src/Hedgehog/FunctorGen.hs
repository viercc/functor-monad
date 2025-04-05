{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Hedgehog.FunctorGen where

import Hedgehog hiding (Var)

import Control.Applicative (Alternative)
import Control.Monad
import Control.Monad.Trans.State.Strict (StateT(..))
import Data.Functor.Sum (Sum (..))
import qualified Hedgehog.Gen as Gen
import Data.Functor.Product (Product(..))
import qualified Hedgehog.Range as Range
import Data.Functor.Identity (Identity(..))
import Hedgehog.Internal.Gen (generalize)
import Data.Functor.Compose (Compose (..))
import FFunctor (type (~>))

-- Util

newtype UniqT m a = UniqT { unUniqT :: Int -> m (a, Int) }
   deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadGen)
     via (StateT Int m)

evalUniqT :: Functor m => UniqT m a -> m a
evalUniqT (UniqT ma) = fst <$> ma 0

var :: Applicative m => UniqT m Int
var = UniqT $ \ i ->
  let i' = i + 1
  in i' `seq` pure (i, i')

-- FGen

newtype FGen t = FGen { runFGen :: forall m a. MonadGen m => m a -> m (t a) }

hoistFGen :: (t ~> u) -> FGen t -> FGen u
hoistFGen f (FGen enumT) = FGen $ \genA -> f <$> enumT genA

skolem :: MonadGen m => FGen t -> m (t Int)
skolem (FGen enumT) = evalUniqT (enumT var)

identityF :: FGen Identity
identityF = FGen $ fmap Identity

pairF :: Gen a -> FGen ((,) a)
pairF genA = FGen $ \genB -> (,) <$> fromGenT (generalize genA) <*> genB

maybeF :: FGen Maybe
maybeF = FGen Gen.maybe

listF :: FGen []
listF = FGen $ Gen.list (Range.linear 0 3)

sumFGen :: FGen t -> FGen u -> FGen (Sum t u)
sumFGen (FGen enumT) (FGen enumU) = FGen $ \genA ->
  Gen.choice
    [ InL <$> enumT genA
    , InR <$> enumU genA
    ]

prodFGen :: FGen t -> FGen u -> FGen (Product t u)
prodFGen (FGen enumT1) (FGen enumT2) = FGen $ \genA ->
  Pair <$> enumT1 genA <*> enumT2 genA

composeFGen :: FGen t -> FGen u -> FGen (Compose t u)
composeFGen (FGen enumT) (FGen enumU) = FGen $ \genA ->
  Compose <$> enumT (enumU genA)

-- * FFGen

newtype FFGen ff = FFGen { runFFGen :: forall t. (Functor t) => FGen t -> FGen (ff t) }