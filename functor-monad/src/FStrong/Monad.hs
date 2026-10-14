{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module FStrong.Monad where

import Data.Functor.Day
import Data.Functor.Day.Curried

import FFunctor
import FMonad
import FStrong

import Data.Functor.Compose
import Data.Functor.Precompose ( Precompose(..) )
import Data.Functor.Bicompose ( Bicompose(..) )
import Control.Monad.Trans.Identity (IdentityT (..))
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Trans.State (StateT (..))
import Control.Monad.Trans.Writer (WriterT (..))
import Data.Functor.Day.Comonoid (Comonoid)

-- | 'FStrongMonad' is an @FMonad@ that is simultaneously 'FStrong',
--   such that they satisfy compatibility conditions -- @FStrongMonad@ laws.
-- 
-- /Compatibility with @fpure@/:
--
--     @
--     'fstrength' . 'trans1' 'fpure' = fpure
--         :: Day h ctx ~> ff (Day h ctx)
--     @
--
-- /Compatibility with @fjoin@/:
--
--     @
--     'fstrength' . 'trans1' 'fjoin'
--       = fjoin . 'ffmap' fstrength . fstrength
--         :: Day (ff (ff h)) ctx ~> ff (Day h ctx) 
--     @
--
class (FStrong mm, FMonad mm) => FStrongMonad mm where
  {-# MINIMAL #-}
  -- | Monadic 'fbind' in terms of 'Curried'.
  --
  -- 'fbindCurried' is derived from @FStrong mm@ and @FMonad mm@ as follows.
  --
  -- > fbindCurried k = ffmap fjoin (mapCurried k)
  -- 
  -- Compatibility conditions show @fbindCurried@ satisfy @Curried@-version of
  -- monad laws.
  fbindCurried :: (Functor g, Functor h) =>
    Curried g (mm h) ~> Curried (mm g) (mm h)
  fbindCurried k = ffmap fjoin (mapCurried k)
  
  -- | 'fbind' with context added.
  -- 
  -- 'sfbind' is derived from @FStrong mm@ and @FMonad mm@ as follows.
  --
  -- > sfbind k = fbind k . fstrength
  sfbind :: (Functor g, Functor h) => 
    (Day g ctx ~> mm h) -> (Day (mm g) ctx ~> mm h)
  sfbind k = fbind k . fstrength

-- * Strong monad induces lax monoidal functor structure

-- | An instance of @FStrongMonad mm@ induces a \"lax monoidal functor\" structure on @mm@,
--   which means a 'Day' convolution product of two @mm g, mm h@ values can be combined to
--   get one @mm (Day g h)@ value.
fap :: (FStrongMonad mm, Functor g, Functor h) => Day (mm g) (mm h) ~> mm (Day g h)
fap = sfbind fstrength'

-- | An instance of @FStrongMonad mm@ can lift @g@, a monoid (with respect to @Day@), to another monoid @mm g@.
--   Here, a monoid (with respect to @Day@) is equivalent way to say @g@ is an @Applicative@. 
liftA2Default :: (FStrongMonad mm, Applicative g) => (a -> b -> c) -> mm g a -> mm g b -> mm g c
liftA2Default op ma mb = sfbind (ffmap dap . fstrength') $ Day ma mb op

pureDefault :: (FMonad mm, Applicative g) => a -> mm g a
pureDefault = fpure . pure

----
-- Instances
----

instance FStrongMonad IdentityT
instance Applicative f => FStrongMonad (Day f)
instance Comonoid f => FStrongMonad (Curried f)
instance Monad f => FStrongMonad (Compose f)
instance Monad f => FStrongMonad (Precompose f)
instance (Monad f, Monad f') => FStrongMonad (Bicompose f f')
instance FStrongMonad (ReaderT e)
instance Monoid m => FStrongMonad (WriterT m)
instance Monoid s => FStrongMonad (StateT s)
