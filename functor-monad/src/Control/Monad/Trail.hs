{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | 'Trail' type which makes an ordinary 'Monad' out of 'FMonad'
module Control.Monad.Trail (Trail (..)) where

import Control.Monad (ap)
import Data.Bifunctor
import FMonad

-- | For any @'FMonad' mm@, @Trail mm@ is a 'Monad'.
--
-- ==== Example
--
-- @Trail mm@ can become variantions of @Monad@ for different @FMonad mm@.
--
-- * @mm = 'Data.Functor.Compose.Compose' m@
--
--     For any @Monad m@, @Trail (Compose m)@ is isomorphic to @m@.
--
--     @
--     Trail (Compose m) a
--       ~ Compose m ((,) a) ()
--       ~ m (a, ())
--       ~ m a
--     @
--
-- * @mm = 'Control.Monad.Free.Free'@
--
--     @Trail Free@ is isomorphic to the list monad @[]@.
--
--     @
--     Trail Free a
--       ~ Free ((,) a) ()
--       ~ [a]
--     @
--
--
-- * @mm = 'FMonad.FreeT.FreeT'' m@
--
--     For any @Monad m@, @Trail (FreeT' m)@ is isomorphic to @ListT m@,
--     where @ListT@ is so-called \"ListT done right.\"
--
--     @
--     Trail (FreeT' m) a
--       ~ FreeT ((,) a) m ()
--       ~ ListT m a
--     @
--
--     See more for examples\/ListTVia.hs
newtype Trail mm a = Trail {runTrail :: mm ((,) a) ()}

instance (FFunctor mm) => Functor (Trail mm) where
  fmap f = Trail . ffmap (first f) . runTrail

-- f :: a -> b
-- first f :: forall c. (a, c) -> (b, c)

instance (FMonad mm) => Applicative (Trail mm) where
  pure a = Trail $ fpure (a, ())
  (<*>) = ap

instance (FMonad mm) => Monad (Trail mm) where
  ma >>= k = Trail . fjoin . ffmap (plug . first (runTrail . k)) . runTrail $ ma

plug :: forall f x. Functor f => (f (), x) -> f x
plug (f_, a) = a <$ f_
