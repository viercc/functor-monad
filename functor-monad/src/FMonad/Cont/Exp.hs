{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module FMonad.Cont.Exp(
  Cont(..)
) where

import FFunctor
import FMonad

import Data.Functor.Exp

-- | \"Continuation monad\" using 'Exp1'.
newtype Cont k f a = Cont { runCont :: ((f `Exp1` k) `Exp1` k) a }
    deriving Functor

flmap :: (f ~> g) -> Exp1 g h ~> Exp1 f h
flmap fg gh = Exp1 $ \f ar -> unExp1 gh (fg f) ar

instance FFunctor (Cont k) where
  ffmap gh (Cont gkk) = Cont $ flmap (flmap gh) gkk

unit :: Functor g => g ~> ((g `Exp1` k) `Exp1` k)
unit gx = Exp1 $ \gk ar -> unExp1 gk (ar <$> gx) id

instance FMonad (Cont k) where
  fpure :: Functor g => g ~> Cont k g
  fpure gx = Cont (unit gx)

  fbind :: forall g h a. (Functor g, Functor h) => (g ~> Cont k h) -> Cont k g a -> Cont k h a
  fbind rest (Cont gkk) =
    let hkkkk :: ((((h `Exp1` k) `Exp1` k) `Exp1` k) `Exp1` k) a
        hkkkk = flmap (flmap (runCont . rest)) gkk

        hkk = flmap unit hkkkk
    in Cont hkk
