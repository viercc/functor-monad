{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module FFunctor.Instances.Free where

import {-# SOURCE #-} FFunctor

import qualified Control.Applicative.Free as FreeAp
import qualified Control.Applicative.Free.Final as FreeApFinal
import qualified Control.Applicative.Trans.FreeAp as FreeApT
import qualified Control.Monad.Free as FreeM
import qualified Control.Monad.Free.Church as FreeMChurch

import Control.Comonad.Cofree (Cofree, hoistCofree)
import Data.Functor.Flip1

instance FFunctor FreeM.Free where
  ffmap = FreeM.hoistFree

instance FFunctor FreeMChurch.F where
  ffmap = FreeMChurch.hoistF

instance FFunctor FreeAp.Ap where
  ffmap = FreeAp.hoistAp

instance FFunctor FreeApFinal.Ap where
  ffmap = FreeApFinal.hoistAp

instance FFunctor (FreeApT.ApT f) where
  ffmap = FreeApT.hoistApT

instance Functor g => FFunctor (Flip1 FreeApT.ApT g) where
  ffmap f2g = Flip1 . FreeApT.transApT f2g . unFlip1

instance FFunctor Cofree where
  ffmap = hoistCofree