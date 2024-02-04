{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module FMonad.Cont.Curried(
  Cont(..)
) where

import FFunctor
import FMonad

import Data.Functor.Day.Curried

-- | \"Continuation monad\" using 'Curried'.
newtype Cont k f a = Cont { runCont :: ((f `Curried` k) `Curried` k) a }
    deriving Functor

flmap :: (f ~> g) -> ((g `Curried` h) ~> (f `Curried` h))
flmap fg gh = Curried $ \f -> runCurried gh (fg f)

instance FFunctor (Cont k) where
  ffmap gh (Cont gkk) = Cont $ flmap (flmap gh) gkk

unit :: Functor g => g ~> ((g `Curried` k) `Curried` k)
unit gx = Curried $ \gk -> runCurried gk (flip ($) <$> gx)

instance FMonad (Cont k) where
  fpure :: Functor g => g ~> Cont k g
  fpure gx = Cont (unit gx)

  fbind :: forall g h a. (Functor g, Functor h) => (g ~> Cont k h) -> Cont k g a -> Cont k h a
  fbind rest (Cont gkk) =
    let hkkkk :: ((((h `Curried` k) `Curried` k) `Curried` k) `Curried` k) a
        hkkkk = flmap (flmap (runCont . rest)) gkk

        hkk = flmap unit hkkkk
    in Cont hkk
