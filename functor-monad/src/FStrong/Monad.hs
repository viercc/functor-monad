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

-- | @'FStrongMonad' mm@ is both @FStrong mm@ and @FMonad mm@,
--   and they satisfy compatibility conditions -- @FStrongMonad@ laws.
--
-- **TODO** Laws
class (FStrong mm, FMonad mm) => FStrongMonad mm where
  {-# MINIMAL #-}
  -- | 'fbind' with context added.
  sfbind :: (Functor g, Functor h) => 
    (Day g ctx ~> mm h) -> (Day (mm g) ctx ~> mm h)
  sfbind k = fbind k . fstrength

-- | Cf. 'Control.Monad.ap'
fap :: (FStrongMonad mm, Functor g, Functor h) => Day (mm g) (mm h) ~> mm (Day g h)
fap = sfbind fstrength'

liftA2Default :: (FStrongMonad mm, Applicative g) => (a -> b -> c) -> mm g a -> mm g b -> mm g c
liftA2Default op ma mb = sfbind (ffmap dap . fstrength') $ Day ma mb op

pureDefault :: (FMonad mm, Applicative g) => a -> mm g a
pureDefault = fpure . pure


instance FStrongMonad IdentityT

instance Applicative f => FStrongMonad (Day f)

instance Comonoid f => FStrongMonad (Curried f)

instance Monad f => FStrongMonad (Compose f)
instance Monad f => FStrongMonad (Precompose f)
instance (Monad f, Monad f') => FStrongMonad (Bicompose f f')
instance FStrongMonad (ReaderT e)
instance Monoid m => FStrongMonad (WriterT m)
instance Monoid s => FStrongMonad (StateT s)
