{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module FFunctor.Instances.Day where

import {-# SOURCE #-} FFunctor

import Data.Functor.Day
import Data.Functor.Day.Curried

instance FFunctor (Day f) where
  ffmap = trans2

instance Functor f => FFunctor (Curried f) where
  ffmap gh (Curried t) = Curried (gh . t)
