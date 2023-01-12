{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module FStrong where

import Control.Monad.Trans.Identity (IdentityT (..))
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Trans.State (StateT (..))
import Control.Monad.Trans.Writer (WriterT (..))
import Data.Coerce (coerce)
import Data.Functor.Compose
import Data.Functor.Day
import Data.Functor.Day.Curried
import FFunctor
import FFunctor.FCompose
import FMonad.Compose

-- | 'FFunctor' with tensorial strength (with respect to 'Day').
class FFunctor ff => FStrong ff where
  {-# MINIMAL fstrength | mapCurried #-}

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
  -- fstrength . ffmap 'elim2' = 'elim2'
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
  -- For readability, the type constructor @Day@ was replaced to an infix operator @(⊗)@.
  fstrength :: (Functor g) => Day (ff g) h ~> ff (Day g h)
  fstrength (Day ffg h op) =
    runCurried (mapCurried (unapplied h)) (fmap op ffg)

  -- | Internal 'ffmap'.
  --
  -- 'mapCurried' can be seen as @ffmap@ but by using @'Curried' g h@ in place of @g ~> h@.
  --
  -- @
  -- ffmap         :: (g ~> h)       ->  (ff g ~> ff h)
  -- mapCurried    :: (Curried g h)  ~>  (Curried (ff g) (ff h))
  -- @
  --
  -- The existence of 'mapCurried', an \"internal fmap\", is known to be equivalent to the existence of
  -- the 'fstrength'.
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
  mapCurried :: (Functor g, Functor h) => Curried g h ~> Curried (ff g) (ff h)
  mapCurried gh = Curried $ \ffg -> ffmap applied (fstrength (day ffg gh))

-- | 'fstrength' but from left
fstrength' :: (FStrong ff, Functor h) => Day g (ff h) ~> ff (Day g h)
fstrength' = ffmap swapped . fstrength . swapped

innerAp :: (FStrong ff, Applicative h) => ff h (a -> b) -> h a -> ff h b
innerAp ffh h = ffmap dap $ fstrength (day ffh h)

-- | Cf. 'Control.Monad.ap'
fap :: (FStrong mm, FMonad mm, Applicative h) => mm h (a -> b) -> mm h a -> mm h b
fap x y = ffmap dap . fjoin . ffmap fstrength' . fstrength $ day x y

instance FStrong IdentityT where
  fstrength = coerce

instance FStrong (Day f) where
  fstrength = disassoc

instance Functor f => FStrong (Curried f) where
  fstrength = toCurried (trans1 applied . assoc)

instance Functor f => FStrong (Compose f) where
  fstrength (Day (Compose fg) h op) = Compose (fmap (\g -> Day g h op) fg)

instance Functor f => FStrong (ComposePre f) where
  fstrength (Day (ComposePre gf) h op) = ComposePre (Day gf h (\fa b -> fmap (flip op b) fa))

instance (Functor f, Functor f') => FStrong (ComposeBoth f f') where
  fstrength (Day (ComposeBoth fgf') h op) =
    ComposeBoth $
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
