{-# LANGUAGE RankNTypes, DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification, GADTSyntax #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
module Data.Functor.Kan.Monad where

import Data.Functor.Kan.Ran
import Data.Functor.Kan.Lan

import Data.Coerce

import FFunctor
import FFunctor.FCompose
import FMonad
import FMonad.Compose (ComposePre(..))

-- | A 'FMonad' made from adjunction @'ComposePre' f -| 'Ran' f@.
newtype RanComp f g a = RanComp {
        runRanComp :: forall b. (a -> f b) -> g (f b)
    }
    deriving Functor

-- | @'RanComp' f@ is isomorphic to @'Ran' f '⊚' ComposePre f@. In other words, for any @Functor g@,
--   these are isomorphisms.
-- 
-- > RanComp f g ~ (Ran f ⊚ ComposePre f) g
-- >             ~ Ran f (ComposePre f g)
--
-- > toRanComp . fromRanComp == id
-- > fromRanComp . toRanComp == id
fromRanComp :: RanComp f g a -> Ran f (ComposePre f g) a
fromRanComp = coerce

toRanComp :: Ran f (ComposePre f g) a -> RanComp f g a
toRanComp = coerce

instance FFunctor (RanComp f) where
    ffmap gh rak = RanComp $ gh . runRanComp rak

instance FMonad (RanComp f) where
    fpure :: Functor g => g x -> RanComp f g x
    fpure gx = RanComp $ \k -> fmap k gx

    fjoin :: Functor g => RanComp f (RanComp f g) x -> RanComp f g x
    fjoin rr = RanComp $ \k -> runRanComp (runRanComp rr k) id

-- | A 'FMonad' made from adjunction @'Lan' f -| ('ComposePre' f)@
data CompLan f g a where
    CompLan :: (f b -> f a) -> g b -> CompLan f g a

deriving instance Functor f => Functor (CompLan f g)

-- | @'CompLan' f@ is isomorphic to @ComposePre f '⊚' Lan f@. In other words, for any @Functor g@,
--   these are isomorphisms.
--   
-- > CompLan f g ~ (ComposePre f ⊚ Lan f) g
-- >             ~ ComposePre f (Lan f g)
--
-- > toCompLan . fromCompLan == id
-- > fromCompLan . toCompLan == id
fromCompLan :: CompLan f g a -> ComposePre f (Lan f g) a
fromCompLan (CompLan tr ga) = ComposePre (Lan tr ga)

toCompLan :: ComposePre f (Lan f g) a -> CompLan f g a
toCompLan (ComposePre (Lan tr ga)) = CompLan tr ga

instance Functor f => FFunctor (CompLan f) where
    ffmap gh (CompLan tr g) = CompLan tr (gh g)

instance Functor f => FMonad (CompLan f) where
    fpure :: Functor g => g x -> CompLan f g x
    fpure gx = CompLan id gx

    fjoin :: Functor g => CompLan f (CompLan f g) x -> CompLan f g x
    fjoin (CompLan tr (CompLan tr' gx)) = CompLan (tr . tr') gx

-- * Transformer versions

-- | A \"transformer\" version of 'RanComp',
--   made out of composition @'Ran' f '⊚' mm '⊚' 'ComposePre' f@.
newtype RanCompT f mm g a = RanCompT {
        runRanCompT :: forall b. (a -> f b) -> mm (ComposePre f g) b
    }
    deriving Functor

-- | Witness of isomorphism @RanCompT f mm ~ Ran f ⊚ mm ⊚ ComposePre f@

fromRanCompT :: RanCompT f mm g x -> (Ran f ⊚ mm ⊚ ComposePre f) g x 
fromRanCompT = coerce

toRanCompT :: (Ran f ⊚ mm ⊚ ComposePre f) g x -> RanCompT f mm g x
toRanCompT = coerce


instance (Functor f, FFunctor mm) => FFunctor (RanCompT f mm) where
    ffmap gh rak = RanCompT $ ffmap (ComposePre . gh . getComposePre) . runRanCompT rak

instance (Functor f, FMonad mm) => FMonad (RanCompT f mm) where
    fpure gx = RanCompT $ \k -> fpure (ComposePre (fmap k gx))
    fjoin rr = RanCompT $ \k -> fjoin . ffmap (\(ComposePre r) -> runRanCompT r id) $ runRanCompT rr k

-- | A \"transformer\" version of 'CompLan', made out of composition @'ComposePre' f '⊚' mm '⊚' 'Lan' f@.
newtype CompLanT f mm g a = CompLanT { runCompLanT :: mm (Lan f g) (f a) }

deriving instance (Functor f, FFunctor mm) => Functor (CompLanT f mm g)

-- | Witness of isomorphism @CompLanT f mm ~ ComposePre f ⊚ mm ⊚ Lan f@
fromCompLanT :: (FFunctor mm, Functor f, Functor g) => CompLanT f mm g x -> (ComposePre f ⊚ mm ⊚ Lan f) g x 
fromCompLanT = coerce

toCompLanT :: (FFunctor mm, Functor f, Functor g) => (ComposePre f ⊚ mm ⊚ Lan f) g x -> CompLanT f mm g x
toCompLanT = coerce

instance (Functor f, FFunctor mm) => FFunctor (CompLanT f mm) where
    ffmap gh = CompLanT . ffmap (ffmap gh) . runCompLanT

instance (Functor f, FMonad mm) => FMonad (CompLanT f mm) where
    fpure gx = CompLanT . fpure . getComposePre . fromCompLan $ fpure gx
    fjoin ll = CompLanT $ fjoin . ffmap (\(Lan t (CompLanT m)) -> fmap t m) . runCompLanT $ ll