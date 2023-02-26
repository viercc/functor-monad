{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BlockArguments #-}

module Data.Functor.Day.Extra where

import Data.Functor.Day
import Data.Functor.Day.Curried
import Data.Functor.Identity
import FFunctor (type (~>))

import Control.Monad.Trans.Reader
import Control.Comonad.Trans.Env
import Control.Comonad.Trans.Traced
import Control.Monad.Trans.Writer

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

-- * Conversions to Monad/Comonad transformers

dayToEnv :: Functor f => Day ((,) s0) f ~> EnvT s0 f
dayToEnv (Day (s0,b) fc op) = EnvT s0 (op b <$> fc)

envToDay :: EnvT s0 f ~> Day ((,) s0) f 
envToDay (EnvT s0 f) = day (s0, id) f

curriedToReader :: Curried ((,) s0) f ~> ReaderT s0 f
curriedToReader (Curried sf) = ReaderT \s0 -> sf (s0, id)

readerToCurried :: Functor f => ReaderT s0 f ~> Curried ((,) s0) f
readerToCurried (ReaderT sf) = Curried \(s0,k) -> fmap k (sf s0)

dayToTraced :: Functor f => Day ((->) s1) f ~> TracedT s1 f
dayToTraced (Day sb fc op) = TracedT $ fmap (\c s -> op (sb s) c) fc

tracedToDay :: TracedT s1 f ~> Day ((->) s1) f 
tracedToDay (TracedT fk) = Day id fk (\s k -> k s)

curriedToWriter :: Curried ((->) s1) f ~> WriterT s1 f
curriedToWriter (Curried sf) = WriterT $ sf (\s a -> (a,s))

writerToCurried :: Functor f => WriterT s1 f ~> Curried ((->) s1) f
writerToCurried (WriterT fas) = Curried $ \sar -> fmap (\(a,s) -> sar s a) fas
