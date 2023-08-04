{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module FFunctor.Instances.Kan where

import {-# SOURCE #-} FFunctor

import Data.Functor.Kan.Lan
import Data.Functor.Kan.Ran

instance FFunctor (Ran f) where
  ffmap gh (Ran ran) = Ran (gh . ran)

instance FFunctor (Lan f) where
  ffmap gh (Lan e g) = Lan e (gh g)
