{-# LANGUAGE
  RankNTypes,
  QuantifiedConstraints,
  ExistentialQuantification,
  TypeOperators,
  PolyKinds,
  
  StandaloneKindSignatures
#-}
module FFunctor(
  type (~>),
  FUNCTOR, FF,
  FFunctor(..)
) where

import Data.Kind ( Type, Constraint )

import Data.Functor.Sum
import Data.Functor.Product
import Data.Functor.Compose

import Data.Functor.Kan.Ran
import Data.Functor.Kan.Lan
import Data.Functor.Day
import Data.Functor.Day.Curried

import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import Control.Monad.Trans.State
import Control.Applicative.Lift

import qualified Control.Monad.Free       as FreeM
import qualified Control.Monad.Free.Church as FreeMChurch
import qualified Control.Applicative.Free as FreeAp
import qualified Control.Applicative.Free.Final as FreeApFinal

-- | Natural transformation arrow
type (~>) :: (k -> Type) -> (k -> Type) -> Type
type (~>) f g = forall x. f x -> g x

{-| Endofunctors on the category of 'Functor's

FFunctor laws:

[Identity]

    >  ffmap id = id

[Composition]

    >  ffmap f . ffmap g = ffmap (f . g)

==== Examples

@FFunctor@ instance of 'Sum' is defined as below:

> data Sum f g a = InL (f a) | InR (g a)
> 
> instance (Functor f) => FFunctor (Sum f) where
>     ffmap :: (Functor g, Functor h) => (g ~> h) -> (Sum f g x -> Sum f h x)
>     ffmap gh fgx = case fgx of
>         InL fx -> InL fx
>         InR gx -> InR (gh gx)

Which can be said  @Functor (Either a)@ but each component is a @Functor@.

==== @ContT@ is not an instance of @FFunctor@

@'Control.Monad.Trans.Cont.ContT' r@ has the kind matching to @FFunctor@, that is, taking a type constructor
@m :: Type -> Type@ and make @ContT r m :: Type -> Type@. But there can't be an instance @FFunctor (ContT r)@,
because @ContT r m@ uses @m@ in both positive and negative positions.

> newtype ContT r m a = ContT {
>     runContT :: (a -> m r) -> m r
>     --                ^       ^ positive position
>     --                | negative position
>   }

-}

-- | The kind of a @Functor@
type FUNCTOR = Type -> Type

-- | The kind of a @FFunctor@.
type FF = FUNCTOR -> FUNCTOR

type  FFunctor :: FF -> Constraint
class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
    ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g x -> ff h x)

instance Functor f => FFunctor (Sum f) where
    ffmap _  (InL fa) = InL fa
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
