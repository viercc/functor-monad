{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Data.Functor.Kan.Monad where

import Data.Coerce
import Data.Functor.Kan.Lan
import Data.Functor.Kan.Ran
import FFunctor
import FFunctor.FCompose
import FMonad
import Data.Functor.Precompose (Precompose (..))

-- | A 'FMonad' made from adjunction @'Precompose' f -| 'Ran' f@.
newtype RanComp f g a = RanComp
  { runRanComp :: forall b. (a -> f b) -> g (f b)
  }
  deriving (Functor)

-- | @'RanComp' f@ is isomorphic to @'Ran' f '⊚' Precompose f@. In other words, for any @Functor g@,
--   these are isomorphisms.
--
-- > RanComp f g ~ (Ran f ⊚ Precompose f) g
-- >             ~ Ran f (Precompose f g)
--
-- > toRanComp . fromRanComp == id
-- > fromRanComp . toRanComp == id
fromRanComp :: RanComp f g a -> Ran f (Precompose f g) a
fromRanComp = coerce

toRanComp :: Ran f (Precompose f g) a -> RanComp f g a
toRanComp = coerce

instance FFunctor (RanComp f) where
  ffmap gh rak = RanComp $ gh . runRanComp rak

instance FMonad (RanComp f) where
  fpure :: Functor g => g x -> RanComp f g x
  fpure gx = RanComp $ \k -> fmap k gx

  fjoin :: Functor g => RanComp f (RanComp f g) x -> RanComp f g x
  fjoin rr = RanComp $ \k -> runRanComp (runRanComp rr k) id

-- | A 'FMonad' made from adjunction @'Lan' f -| ('Precompose' f)@
data CompLan f g a where
  CompLan :: (f b -> f a) -> g b -> CompLan f g a

deriving instance Functor f => Functor (CompLan f g)

-- | @'CompLan' f@ is isomorphic to @Precompose f '⊚' Lan f@. In other words, for any @Functor g@,
--   these are isomorphisms.
--
-- > CompLan f g ~ (Precompose f ⊚ Lan f) g
-- >             ~ Precompose f (Lan f g)
--
-- > toCompLan . fromCompLan == id
-- > fromCompLan . toCompLan == id
fromCompLan :: CompLan f g a -> Precompose f (Lan f g) a
fromCompLan (CompLan tr ga) = Precompose (Lan tr ga)

toCompLan :: Precompose f (Lan f g) a -> CompLan f g a
toCompLan (Precompose (Lan tr ga)) = CompLan tr ga

instance Functor f => FFunctor (CompLan f) where
  ffmap gh (CompLan tr g) = CompLan tr (gh g)

instance Functor f => FMonad (CompLan f) where
  fpure :: Functor g => g x -> CompLan f g x
  fpure gx = CompLan id gx

  fjoin :: Functor g => CompLan f (CompLan f g) x -> CompLan f g x
  fjoin (CompLan tr (CompLan tr' gx)) = CompLan (tr . tr') gx

-- * Transformer versions

-- | A \"transformer\" version of 'RanComp',
--   made out of composition @'Ran' f '⊚' mm '⊚' 'Precompose' f@.
newtype RanCompT f mm g a = RanCompT
  { runRanCompT :: forall b. (a -> f b) -> mm (Precompose f g) b
  }
  deriving (Functor)

-- | Witness of isomorphism @RanCompT f mm ~ Ran f ⊚ mm ⊚ Precompose f@
fromRanCompT :: RanCompT f mm g x -> (Ran f ⊚ mm ⊚ Precompose f) g x
fromRanCompT = coerce

toRanCompT :: (Ran f ⊚ mm ⊚ Precompose f) g x -> RanCompT f mm g x
toRanCompT = coerce

instance (Functor f, FFunctor mm) => FFunctor (RanCompT f mm) where
  ffmap gh rak = RanCompT $ ffmap (Precompose . gh . getPrecompose) . runRanCompT rak

instance (Functor f, FMonad mm) => FMonad (RanCompT f mm) where
  fpure gx = RanCompT $ \k -> fpure (Precompose (fmap k gx))
  fjoin rr = RanCompT $ \k -> fjoin . ffmap (\(Precompose r) -> runRanCompT r id) $ runRanCompT rr k

-- | A \"transformer\" version of 'CompLan', made out of composition @'Precompose' f '⊚' mm '⊚' 'Lan' f@.
newtype CompLanT f mm g a = CompLanT {runCompLanT :: mm (Lan f g) (f a)}

deriving instance (Functor f, FFunctor mm) => Functor (CompLanT f mm g)

-- | Witness of isomorphism @CompLanT f mm ~ Precompose f ⊚ mm ⊚ Lan f@
fromCompLanT :: (FFunctor mm, Functor f, Functor g) => CompLanT f mm g x -> (Precompose f ⊚ mm ⊚ Lan f) g x
fromCompLanT = coerce

toCompLanT :: (FFunctor mm, Functor f, Functor g) => (Precompose f ⊚ mm ⊚ Lan f) g x -> CompLanT f mm g x
toCompLanT = coerce

instance (Functor f, FFunctor mm) => FFunctor (CompLanT f mm) where
  ffmap gh = CompLanT . ffmap (ffmap gh) . runCompLanT

instance (Functor f, FMonad mm) => FMonad (CompLanT f mm) where
  fpure gx = CompLanT . fpure . getPrecompose . fromCompLan $ fpure gx
  fjoin ll = CompLanT $ fjoin . ffmap (\(Lan t (CompLanT m)) -> fmap t m) . runCompLanT $ ll
