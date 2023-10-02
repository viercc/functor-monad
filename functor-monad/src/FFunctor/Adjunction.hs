{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE BlockArguments #-}
module FFunctor.Adjunction (Adjunction(..)) where


import Data.Coerce ( coerce, Coercible )
import Data.Kind (Constraint)

import Control.Monad.Trans.Identity
import Data.Functor.Day
import Data.Functor.Day.Curried

import Data.Functor.Kan.Lan
import Data.Functor.Kan.Ran
import Data.Functor.Precompose (Precompose(..))
import Data.Functor.Compose (Compose(..))

import qualified Data.Bifunctor.Sum as Bi
import qualified Data.Bifunctor.Product as Bi
import qualified Data.Bifunctor.Product.Extra as Bi

import qualified Data.Functor.Adjunction as Rank1
import qualified Control.Monad.Trans.Reader as Rank1
import qualified Control.Monad.Trans.Writer as Rank1
import qualified Control.Monad.Trans.State.Lazy as Rank1
import qualified Control.Comonad.Trans.Env as Rank1
import qualified Control.Comonad.Trans.Traced as Rank1
import qualified Control.Comonad.Trans.Store as Rank1

import FFunctor
import FFunctor.FCompose ( FCompose(..) )

-- | An adjunction between \(\mathrm{Hask}^{\mathrm{Hask}}\) and \(\mathrm{Hask}^{\mathrm{Hask}}\).
type Adjunction :: FF -> FF -> Constraint
class (FFunctor ff, FFunctor uu) => Adjunction ff uu | ff -> uu, uu -> ff where
    {-# MINIMAL (unit, counit) | (leftAdjunct, rightAdjunct) #-}
    unit :: forall g. Functor g => g ~> uu (ff g)
    unit = leftAdjunct id
    counit :: forall g. Functor g => ff (uu g) ~> g
    counit = rightAdjunct id

    leftAdjunct :: forall g h. (Functor g, Functor h) => (ff g ~> h) -> (g ~> uu h)
    leftAdjunct ffg_h = ffmap ffg_h . unit
    rightAdjunct :: forall g h. (Functor g, Functor h) => (g ~> uu h) -> (ff g ~> h)
    rightAdjunct g_uuh = counit . ffmap g_uuh

natCoerce :: forall f' f g g'. (Coercible f' f, Coercible g g') => (f ~> g) -> (f' ~> g')
natCoerce fg =
    let f'g' :: forall x. f' x -> g' x
        f'g' = coerce (fg @x)
    in f'g'

instance Adjunction IdentityT IdentityT where
    unit = coerce
    counit = coerce
    leftAdjunct = natCoerce 
    rightAdjunct = natCoerce

instance Functor f => Adjunction (Day f) (Curried f) where
    unit = unapplied
    counit = applied

    leftAdjunct = toCurried
    rightAdjunct = fromCurried

instance Functor f => Adjunction (Lan f) (Precompose f) where
    unit :: (Functor g) => g ~> Precompose f (Lan f g)
    unit g = Precompose $ Lan id g
    counit :: (Functor g) => Lan f (Precompose f g) ~> g
    counit (Lan unF (Precompose gf)) = fmap unF gf

instance Functor f => Adjunction (Precompose f) (Ran f) where
    unit :: (Functor g) => g ~> Ran f (Precompose f g)
    -- g ~> Ran f (g :.: f)
    -- ∀x. g x -> (∀y. (x -> f y) -> g (f y))
    unit g = Ran $ \toF -> Precompose (fmap toF g)

    counit :: (Functor g) => Precompose f (Ran f g) ~> g
    -- Ran f g :.: f ~> g
    -- ∀x. (∀y. (f x -> f y) -> g y) -> g x
    counit (Precompose ffg) = runRan ffg id

instance (Adjunction ff uu, Adjunction gg vv) => Adjunction (FCompose ff gg) (FCompose vv uu) where
    unit :: Functor h => h ~> FCompose vv uu (FCompose ff gg h)
    unit = ffmap FCompose . FCompose . ffmap unit . unit

    counit :: Functor h => FCompose ff gg (FCompose vv uu h) ~> h
    counit = counit . ffmap counit . getFCompose . ffmap getFCompose

    leftAdjunct :: forall h k. (Functor h, Functor k)
      => (FCompose ff gg h ~> k) -> h ~> FCompose vv uu k
    leftAdjunct lefty = FCompose . leftAdjunct (leftAdjunct (lefty . FCompose))

    rightAdjunct :: (Functor h, Functor k)
      => (h ~> FCompose vv uu k) -> FCompose ff gg h ~> k
    rightAdjunct righty = rightAdjunct (rightAdjunct (getFCompose . righty)) . getFCompose

instance (Adjunction ff uu, Adjunction gg vv) => Adjunction (Bi.Sum ff gg) (Bi.Product uu vv) where
    unit :: (Functor h)
      => h ~> Bi.Product uu vv (Bi.Sum ff gg h)
    unit h = Bi.Pair (ffmap Bi.L2 (unit h)) (ffmap Bi.R2 (unit h))

    counit :: (Functor h)
      => Bi.Sum ff gg (Bi.Product uu vv h) ~> h
    counit (Bi.L2 ffP) = counit (ffmap Bi.proj1 ffP)
    counit (Bi.R2 ggP) = counit (ffmap Bi.proj2 ggP)

    leftAdjunct :: (Functor h, Functor k) => (Bi.Sum ff gg h ~> k) -> h ~> Bi.Product uu vv k
    leftAdjunct lefty h = Bi.Pair (leftAdjunct (lefty . Bi.L2) h) (leftAdjunct (lefty . Bi.R2) h)

    rightAdjunct :: (Functor h, Functor k) => (h ~> Bi.Product uu vv k) -> Bi.Sum ff gg h ~> k
    rightAdjunct righty (Bi.L2 ff) = rightAdjunct (Bi.proj1 . righty) ff
    rightAdjunct righty (Bi.R2 gg) = rightAdjunct (Bi.proj2 . righty) gg

instance (Rank1.Adjunction f u) => Adjunction (Compose f) (Compose u) where
    unit :: (Functor g) => g ~> Compose u (Compose f g)
    unit gx = Compose . fmap Compose $ Rank1.unit gx
    counit :: (Functor g) => Compose f (Compose u g) ~> g
    counit = Rank1.counit . fmap getCompose . getCompose

instance Adjunction (Rank1.EnvT e) (Rank1.ReaderT e) where
    unit gx = Rank1.ReaderT \e -> Rank1.EnvT e gx
    counit (Rank1.EnvT e (Rank1.ReaderT f)) = f e

instance Adjunction (Rank1.TracedT m) (Rank1.WriterT m) where
    unit gx = Rank1.WriterT $ Rank1.TracedT $ fmap (,) gx

    counit (Rank1.TracedT (Rank1.WriterT gwx)) = fmap (\(f, m) -> f m) gwx

instance Adjunction (Rank1.StoreT s) (Rank1.StateT s) where
    unit gx = Rank1.StateT $ Rank1.StoreT (fmap (,) gx)
    counit (Rank1.StoreT (Rank1.StateT state) s0) = fmap (\(f, m) -> f m) (state s0)