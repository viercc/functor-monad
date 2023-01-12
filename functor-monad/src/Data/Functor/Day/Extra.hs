{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Data.Functor.Day.Extra where

import Data.Functor.Day
import Data.Functor.Day.Curried
import Data.Functor.Identity
import FFunctor (type (~>))

-- @'uncurry' :: (a -> b -> c) -> (a,b) -> c@
uncurried :: forall f g h c. (Functor f, Functor g) => Curried f (Curried g h) c -> Curried (Day f g) h c
uncurried = toCurried (applied . trans2 applied . disassoc . trans1 swapped)

-- @'curry' :: ((a,b) -> c) -> (a -> b -> c)@
curried :: forall f g h c. (Functor f, Functor g) => Curried (Day f g) h c -> Curried f (Curried g h) c
curried = toCurried (toCurried (applied . trans1 swapped . assoc))

-- | Internal identity of natural transformation.
--
-- @ unitCurried = 'toCurried' 'elim2' @
unitCurried :: Functor g => Identity ~> Curried g g
unitCurried = toCurried elim2

-- | Internal composition of natural transformations.
--
-- @ composeCurried = 'toCurried' ('applied' . 'trans1' 'applied' . 'assoc') @
composeCurried :: (Functor f, Functor g, Functor h) => Day (Curried f g) (Curried g h) ~> Curried f h
composeCurried = toCurried (applied . trans1 applied . assoc)
