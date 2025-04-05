{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TypeOperators #-}
module FFunctor.Law where

import FFunctor

import Hedgehog
import Hedgehog.FunctorGen

ffmap_id :: (FFunctor ff, Functor g, Eq (ff g Int), Show (ff g Int)) => FGen (ff g) -> Property
ffmap_id gen = property do
  ff <- forAll (skolem gen)
  ffmap id ff === ff

ffmap_comp :: (FFunctor ff, Traversable g, Traversable h, Functor k)
  => (Show (ff g Int))
  => (Eq (ff k Int), Show (ff k Int))
  => (h ~> k) -> (g ~> h) -> FGen (ff g) -> Property
ffmap_comp hk gh gen = property do
  ff <- forAll (skolem gen)
  ffmap (hk . gh) ff === ffmap hk (ffmap gh ff)