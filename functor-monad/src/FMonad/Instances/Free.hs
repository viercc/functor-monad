{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module FMonad.Instances.Free where

import {-# SOURCE #-} FMonad
import FFunctor.Instances.Free()

import qualified Control.Applicative.Free as FreeAp
import qualified Control.Applicative.Free.Final as FreeApFinal
import qualified Control.Applicative.Trans.FreeAp as FreeApT
import qualified Control.Monad.Free as FreeM
import qualified Control.Monad.Free.Church as FreeMChurch

import Data.Functor.Flip1

instance FMonad FreeM.Free where
  fpure = FreeM.liftF
  fbind = FreeM.foldFree

instance FMonad FreeMChurch.F where
  fpure = FreeMChurch.liftF
  fbind = FreeMChurch.foldF

instance FMonad FreeAp.Ap where
  fpure = FreeAp.liftAp
  fbind = FreeAp.runAp

instance FMonad FreeApFinal.Ap where
  fpure = FreeApFinal.liftAp
  fbind = FreeApFinal.runAp

instance FMonad (FreeApT.ApT f) where
  fpure = FreeApT.liftT
  fbind k = FreeApT.fjoinApTLeft . ffmap k

instance Applicative g => FMonad (Flip1 FreeApT.ApT g) where
  fpure = Flip1 . FreeApT.liftF
  fbind k = Flip1 . FreeApT.foldApT (unFlip1 . k) FreeApT.liftT . unFlip1
