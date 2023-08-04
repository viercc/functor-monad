{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module FMonad.Instances.Day where

import {-# SOURCE #-} FMonad
import FFunctor.Instances.Day()

import Data.Functor.Day
import Data.Functor.Day.Comonoid
import Data.Functor.Day.Curried
import Data.Functor.Day.Extra (uncurried)

instance (Applicative f) => FMonad (Day f) where
  fpure :: g ~> Day f g
  fpure = day (pure id)

  {-
     day :: f (a -> b) -> g a -> Day f g b
  -}
  
  fbind k = trans1 dap . assoc . trans2 k

  {-
    trans2 k   :: Day f g ~> Day f (Day f h)
    assoc      ::            Day f (Day f h) ~> Day (Day f f) h
    trans1 dap ::                               Day (Day f f) h ~> Day f h
  -}

instance Comonoid f => FMonad (Curried f) where
  fpure :: Functor g => g a -> Curried f g a
  fpure g = Curried $ \f -> extract f <$> g

  fbind k m = Curried $ \f -> runCurried (uncurried (ffmap k m)) (coapply f)
