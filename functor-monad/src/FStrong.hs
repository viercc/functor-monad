{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

-- | 'FFunctor' with tensorial strength with respect to 'Day'.
module FStrong where

import Data.Coerce (coerce)

import Data.Functor.Day
import Data.Functor.Day.Curried

import FFunctor

import Data.Functor.Compose
import FFunctor.FCompose
import Data.Functor.Precompose ( Precompose(..) )
import Data.Functor.Bicompose ( Bicompose(..) )
import Control.Monad.Trans.Identity (IdentityT (..))
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Trans.State (StateT (..))
import Control.Monad.Trans.Writer (WriterT (..))
import Control.Comonad.Env (EnvT(..))
import Control.Comonad.Traced (TracedT(..))
import Control.Comonad.Store (StoreT (..))

-- | 'FFunctor' with tensorial strength with respect to 'Day'.
class FFunctor ff => FStrong ff where
  {-# MINIMAL fstrength | fstrengthR | mapCurried #-}

  -- | Tensorial strength with respect to 'Day'.
  --
  -- 'fstrength' can be thought as a higher-order version of @strength@ function below.
  --
  -- @
  -- strength :: Functor f => (f a, b) -> f (a, b)
  -- strength (fa, b) = fmap (\a -> (a,b)) fa
  -- @
  --
  -- For the ordinary 'Functor', no additional type classes were needed to have @strength@ function,
  -- because it works for any @Functor f@. This is not the case for 'FFunctor' and 'fstrength'.
  --
  -- ==== Laws
  --
  -- These two equations must hold.
  --
  -- @
  -- ffmap 'elim2' . fstrength  = 'elim2'
  --       :: Day (ff g) 'Data.Functor.Identity.Identity' ~> ff g
  -- fstrength . 'trans1' fstrength = ffmap 'assoc' . fstrength . 'disassoc'
  --       :: Day (Day (ff g) h) k ~> ff (Day (Day g h) k))
  -- @
  --
  -- Alternatively, these diagrams must commute.
  --
  -- >                    fstrength
  -- >  ff g ⊗ Identity ----------->  ff (g ⊗ Identity)
  -- >            \                          |
  -- >             \                         |   ffmap elim2
  -- >              \                        |
  -- >        elim2  \                       v
  -- >                \---------------->   ff g
  --
  --
  -- >                     trans1 fstrength                      fstrength
  -- > (ff g ⊗ h) ⊗ k -------------------->  ff (g ⊗ h) ⊗ k ----------->  ff ((g ⊗ h) ⊗ k)
  -- >            |                                                                   ^
  -- >            | disassoc                                             ffmap assoc  |
  -- >            |                                                                   |
  -- >            v                           fstrength                               |
  -- >  ff g ⊗ (h ⊗ k) --------------------------------------------------->  ff (g ⊗ (h ⊗ k))
  --
  -- For readability, an infix operator @(⊗)@ was used instead of the type constructor @Day@.
  fstrength :: (Functor g) => Day (ff g) h ~> ff (Day g h)
  fstrength (Day ffg h op) =
    runCurried (mapCurried (unapplied h)) (fmap op ffg)

  -- | 'fstrength' but restricted to functions `(->) a`.
  --
  -- The type of 'fstrengthR' does not use `Day` using natural isomorphism between
  -- `Day f ((->) a) r` and `Precompose ((->) f) ≅ f (a -> r)`.
  -- 
  -- ==== Laws
  -- 
  -- 'fstrengthR' must satisfy the equations 'fstrength' satisfies,
  -- under isomorphism converting the type to that of @fstrength@
  -- restriceted to functions:
  -- 
  -- > fstrengthFn = ffmap (fnToDay . getPrecompose) . fstrengthR . dayToFn
  -- >   :: Day (ff g) ((->) a) ~> ff (Day g ((->) a))
  --
  -- where
  --
  -- > dayToFn :: (Functor f) => Day f ((->) b) r -> f (b -> r)
  -- > fnToDay :: (Functor f) => f (b -> r) -> Day f ((->) b) r
  --
  -- ==== Relation to other methods
  -- 
  -- 'fstrengthR' must be equivalent to 'fstrength' under @dayToFn, fnToDay@ isomorphisms.
  -- 
  -- > fstrengthR = ffmap (Precompose . dayToFn) . fstrength . fnToDay
  fstrengthR :: (Functor g) => ff g (a -> x) -> ff (Precompose ((->) a) g) x
  fstrengthR = ffmap (Precompose . dayToFn) . fstrength . fnToDay
    where
      dayToFn :: forall f b r. (Functor f) => Day f ((->) b) r -> f (b -> r)
      dayToFn (Day f bc op) = (\a b -> op a (bc b)) <$> f

      fnToDay :: forall f b r. (Functor f) => f (b -> r) -> Day f ((->) b) r
      fnToDay fbr = Day fbr id id

  -- | Internal 'ffmap'.
  --
  -- 'mapCurried' can be seen as @ffmap@ but by using "internal language" of
  -- \(\mathrm{Hask}^{\mathrm{Hask}}\), the category of @Functor@s.
  --
  -- @
  -- ffmap         :: (g ~> h)       ->  (ff g ~> ff h)
  -- mapCurried    :: (Curried g h)  ~>  (Curried (ff g) (ff h))
  -- @
  --
  -- @ffmap@ takes a natural transformations @(~>)@, in other words morphism in \(\mathrm{Hask}^{\mathrm{Hask}}\),
  -- and returns another @(~>)@. @ffmap@ itself is an usual function, which is an outsider for
  -- \(\mathrm{Hask}^{\mathrm{Hask}}\).
  --
  -- On the other hand, @mapCurried@ is a natural transformation @(~>)@ between @Curried _ _@,
  -- objects of \(\mathrm{Hask}^{\mathrm{Hask}}\).
  -- 
  -- It is known that the set of all (lawful) 'mapCurried' has bijection to the set of all (lawful) 'fstrength'.
  --
  -- ==== Laws
  --
  -- These equations must hold.
  --
  -- @
  -- mapCurried . 'Data.Functor.Day.Extra.unitCurried' = 'Data.Functor.Day.Extra.unitCurried'
  --     :: Identity ~> Curried (ff g) (ff g)
  -- mapCurried . 'Data.Functor.Day.Extra.composeCurried' = 'Data.Functor.Day.Extra.composeCurried' . trans1 mapCurried . trans2 mapCurried
  --     :: Day (Curried g h) (Curried h k) ~> Curried (ff g) (ff k)
  -- @
  --
  -- ==== Relation to other methods
  -- 
  -- 'mapCurried' must be equivalent to the follwing default implementation,
  -- implemented using 'fstrengthR'.
  -- 
  -- > mapCurried gh = Curried $ \ffg -> ffmap (runCurried gh . getPrecompose) (fstrengthR ffg)
  mapCurried :: (Functor g, Functor h) => Curried g h ~> Curried (ff g) (ff h)
  mapCurried gh = Curried $ \ffg -> ffmap (runCurried gh . getPrecompose) (fstrengthR ffg)

  -- | 'fstrength' but from left. 'fstrength'' must be observationally equivalent to
  --   the following default implementation.
  --
  -- > fstrength' = ffmap swapped . fstrength . swapped
  --
  -- It is included for the optimization opportunity.
  fstrength' :: (Functor h) => Day g (ff h) ~> ff (Day g h)
  fstrength' = ffmap swapped . fstrength . swapped

instance FStrong IdentityT where
  fstrength = coerce

instance FStrong (Day f) where
  fstrength = disassoc

instance Functor f => FStrong (Curried f) where
  fstrength = toCurried (trans1 applied . assoc)

instance Functor f => FStrong (Compose f) where
  fstrength (Day (Compose fg) h op) = Compose (fmap (\g -> Day g h op) fg)

instance Functor f => FStrong (Precompose f) where
  fstrength (Day (Precompose gf) h op) = Precompose (Day gf h (\fa b -> fmap (flip op b) fa))

instance (Functor f, Functor f') => FStrong (Bicompose f f') where
  fstrength (Day (Bicompose fgf') h op) =
    Bicompose $
      fmap (\gf' -> Day gf' h (\fa b -> fmap (flip op b) fa)) fgf'

instance FStrong (ReaderT e) where
  fstrength (Day (ReaderT eg) h op) = ReaderT $ \e -> Day (eg e) h op

instance FStrong (WriterT m) where
  fstrength (Day (WriterT gm) h op) = WriterT $ Day gm h (\(b, m) c -> (op b c, m))

instance FStrong (StateT s) where
  -- StateT s = ReaderT s ∘ WriterT s = Compose ((->) s) ∘ WriterT s
  fstrength (Day (StateT sgs) h op) = StateT $ \s -> Day (sgs s) h (\(b, s') c -> (op b c, s'))

instance (FStrong ff, FStrong gg) => FStrong (FCompose ff gg) where
  fstrength = FCompose . ffmap fstrength . fstrength . coerce

instance FStrong (EnvT e) where
  fstrength (Day (EnvT e g) h op) = EnvT e (Day g h op)

instance FStrong (TracedT m) where
  fstrength (Day (TracedT gf) h op) = TracedT (Day gf h (\mb c m -> op (mb m) c))

instance FStrong (StoreT s) where
  fstrength (Day (StoreT gf s) h op) = StoreT (Day gf h (\sb c s' -> op (sb s') c)) s