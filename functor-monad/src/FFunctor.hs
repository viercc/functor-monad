{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}

-- | Functors on the category of @Functor@ s.
module FFunctor
  ( type (~>),
    FFunctor (..),

    -- * Utilities to kind-annotate FFunctor instances
    FUNCTOR,
    FF,
  )
where

import qualified Control.Applicative.Free as FreeAp
import qualified Control.Applicative.Free.Final as FreeApFinal
import Control.Applicative.Lift
import qualified Control.Applicative.Trans.FreeAp as FreeApT
import qualified Control.Monad.Free as FreeM
import qualified Control.Monad.Free.Church as FreeMChurch
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.Functor.Compose
import Data.Functor.Day
import Data.Functor.Day.Curried
import Data.Functor.Flip1
import Data.Functor.Kan.Lan
import Data.Functor.Kan.Ran
import Data.Functor.Product
import Data.Functor.Sum
import Data.Kind (Constraint, Type)

import qualified Data.Bifunctor.Sum as Bi
import qualified Data.Bifunctor.Product as Bi

import Control.Comonad.Env (EnvT(..))
import Control.Comonad.Traced (TracedT(..))
import Control.Comonad.Store (StoreT (..))
import Control.Comonad.Cofree (Cofree, hoistCofree)
import Control.Monad.Trans.Free (FreeT, hoistFreeT)

-- | Natural transformation arrow
type (~>) :: (k -> Type) -> (k -> Type) -> Type
type (~>) f g = forall x. f x -> g x

-- | The kind of a @Functor@
type FUNCTOR = Type -> Type

-- | The kind of a @FFunctor@.
type FF = FUNCTOR -> FUNCTOR

{- | Endofunctors on the category of 'Functor's.

+----------------+-----------------------------+------------------------------------+
|                | @'Functor' f@               | @'FFunctor' ff@                    |
+================+=============================+====================================+
| Takes          | A type @a@                  | A @Functor g@                      |
+----------------+-----------------------------+------------------------------------+
| Makes          | A type @f a@                | A @Functor (ff g)@                 |
+----------------+-----------------------------+------------------------------------+
| Feature        | @                           | @                                  |
|                | fmap                        | ffmap                              |
|                |   :: (a -> b) -> f a -> f b |    :: (Functor g, Functor h)       |
|                | @                           |    => (g ~> h) -> (ff g ~> ff h)   |
|                |                             | @                                  |
+----------------+-----------------------------+------------------------------------+

FFunctor laws:

[Identity]

   >  ffmap id = id

[Composition]

   >  ffmap f . ffmap g = ffmap (f . g)

==== Examples

This is the @FFunctor@ instance of @'Sum' f@.
Just like the 'fmap' from @Functor (Either a)@ instance which applies a function to the \"Right\" value,
@ffmap@ applies @gh :: g ~> h@ to the @InR (g a)@ value.

@
data Sum f g a = InL (f a) | InR (g a)
instance (Functor f) => FFunctor (Sum f) where
    ffmap gh fgx = case fgx of
        InL fx -> InL fx
        InR gx -> InR (gh gx)
@

Like @Sum f@, some instances of @FFunctor@ are modified @Functor@s in such a way that
its parameter is swapped for @g a@.
But not every instance of @FFunctor@ is like this. The following data type @Foo g a@
is a @FFunctor@ which uses a @Functor g@ and a type parameter @a@ separately.

@
data Foo g a = Foo (String -> a) (g String)

instance Functor (Foo g) where
  fmap :: (a -> b) -> Foo g a -> Foo g b
  fmap f (Foo strToA gStr) = Foo (f . strToA) gStr

instance FFunctor Foo where
  ffmap :: (g ~> h) -> Foo g a -> Foo h a
  ffmap gh (Foo strToA gStr) = Foo strToA (gh gStr)
@

An @FFunctor@ instance can use its @Functor@ parameter nested. The following @Bar g a@ example uses
@g@ nested twice.

@
newtype Bar g a = Bar (g (g a))

instance Functor g => Functor (Bar g) where
  fmap f (Bar gga) = Bar $ fmap (fmap f gga)

instance FFunctor Bar where
  ffmap gh (Bar gga) = Bar $ fmap gh (gh gga)
@

==== Non-example

@'Control.Monad.Trans.Cont.ContT' r@ has the right kind to be an @FFunctor@, that is,
@(Type -> Type) -> Type -> Type@. But there can be no instances of @FFunctor (ContT r)@,
because @ContT r m@ uses @m@ in negative position.

> newtype ContT r m a = ContT {
>     runContT :: (a -> m r) -> m r
>     --                ^       ^ positive position
>     --                | negative position
>   }

-}
type FFunctor :: FF -> Constraint
class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
  ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g x -> ff h x)

instance Functor f => FFunctor (Sum f) where
  ffmap _ (InL fa) = InL fa
  ffmap gh (InR ga) = InR (gh ga)

instance Functor f => FFunctor (Product f) where
  ffmap gh (Pair fa ga) = Pair fa (gh ga)

instance Functor f => FFunctor (Compose f) where
  ffmap gh = Compose . fmap gh . getCompose

instance FFunctor Lift where
  ffmap gh = mapLift gh

instance FFunctor FreeM.Free where
  ffmap = FreeM.hoistFree

instance FFunctor FreeMChurch.F where
  ffmap = FreeMChurch.hoistF

instance FFunctor FreeAp.Ap where
  ffmap = FreeAp.hoistAp

instance FFunctor FreeApFinal.Ap where
  ffmap = FreeApFinal.hoistAp

instance FFunctor IdentityT where
  ffmap fg = IdentityT . fg . runIdentityT

instance FFunctor (ReaderT e) where
  ffmap fg = ReaderT . fmap fg . runReaderT

instance FFunctor (WriterT m) where
  ffmap fg = WriterT . fg . runWriterT

instance FFunctor (StateT s) where
  ffmap fg = StateT . fmap fg . runStateT

instance FFunctor (Ran f) where
  ffmap gh (Ran ran) = Ran (gh . ran)

instance FFunctor (Lan f) where
  ffmap gh (Lan e g) = Lan e (gh g)

instance FFunctor (Day f) where
  ffmap = trans2

instance Functor f => FFunctor (Curried f) where
  ffmap gh (Curried t) = Curried (gh . t)

instance FFunctor (FreeApT.ApT f) where
  ffmap = FreeApT.hoistApT

instance Functor f => FFunctor (FreeT f) where
  ffmap = hoistFreeT

instance Functor g => FFunctor (Flip1 FreeApT.ApT g) where
  ffmap f2g = Flip1 . FreeApT.transApT f2g . unFlip1

instance (FFunctor ff, FFunctor gg) => FFunctor (Bi.Sum ff gg) where
  ffmap t (Bi.L2 ff) = Bi.L2 (ffmap t ff)
  ffmap t (Bi.R2 gg) = Bi.R2 (ffmap t gg)

instance (FFunctor ff, FFunctor gg) => FFunctor (Bi.Product ff gg) where
  ffmap t (Bi.Pair ff gg) = Bi.Pair (ffmap t ff) (ffmap t gg)

instance FFunctor (EnvT e) where
  ffmap gh (EnvT e g) = EnvT e (gh g)

instance FFunctor (TracedT m) where
  ffmap gh (TracedT g) = TracedT (gh g)

instance FFunctor (StoreT s) where
  ffmap gh (StoreT g s) = StoreT (gh g) s

instance FFunctor Cofree where
  ffmap = hoistCofree