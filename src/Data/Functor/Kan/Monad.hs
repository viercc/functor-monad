{-# LANGUAGE RankNTypes, DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification, GADTSyntax #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
module Data.Functor.Kan.Monad where

import Data.Functor.Compose
import Data.Functor.Kan.Ran
import Data.Functor.Kan.Lan

import Data.Coerce

import FFunctor
import FMonad

-- | A 'FMonad' made from adjunction @(\`Compose\` f) -| Ran f@
newtype RanComp f g a = RanComp {
        runRanComp :: forall b. (a -> f b) -> g (f b)
    }
    deriving Functor

-- | @'RanComp' f g@ is isomorphic to @'Ran' f ('Compose' g f)@
--
-- > toRanCompose . fromRanCompose == id
-- > fromRanCompose . toRanCompose == id
toRanCompose :: RanComp f g a -> Ran f (Compose g f) a
toRanCompose = coerce

fromRanCompose :: Ran f (Compose g f) a -> RanComp f g a
fromRanCompose = coerce

instance FFunctor (RanComp f) where
    ffmap gh rak = RanComp $ gh . runRanComp rak

instance FMonad (RanComp f) where
    fpure :: Functor g => g x -> RanComp f g x
    fpure gx = RanComp $ \k -> fmap k gx

    fjoin :: Functor g => RanComp f (RanComp f g) x -> RanComp f g x
    fjoin rr = RanComp $ \k -> runRanComp (runRanComp rr k) id

-- | A 'FMonad' made from adjunction @Lan f -| (\`Compose\` f)@
data CompLan f g a where
    CompLan :: (f b -> f a) -> g b -> CompLan f g a

deriving instance Functor f => Functor (CompLan f g)

-- | @'CompLan' f g@ is isomorphic to @Compose ('Lan' f g) f@
--
-- > toComposeLan . fromComposeLan == id
-- > fromComposeLan . toComposeLan == id
toComposeLan :: CompLan f g a -> Compose (Lan f g) f a
toComposeLan (CompLan tr ga) = Compose (Lan tr ga)

fromComposeLan :: Compose (Lan f g) f a -> CompLan f g a
fromComposeLan (Compose (Lan tr ga)) = CompLan tr ga

instance Functor f => FFunctor (CompLan f) where
    ffmap gh (CompLan tr g) = CompLan tr (gh g)

instance Functor f => FMonad (CompLan f) where
    fpure :: Functor g => g x -> CompLan f g x
    fpure gx = CompLan id gx

    fjoin :: Functor g => CompLan f (CompLan f g) x -> CompLan f g x
    fjoin (CompLan tr (CompLan tr' gx)) = CompLan (tr . tr') gx

-- * Transformer versions

-- | A \"transformer\" version of 'RanComp', made out of composition @Ran f ∘ mm ∘ (\`Compose\` f)@.
newtype RanCompT f mm g a = RanCompT {
        runRanCompT :: forall b. (a -> f b) -> mm (Compose g f) b
    }
    deriving Functor

instance (Functor f, FFunctor mm) => FFunctor (RanCompT f mm) where
    ffmap gh rak = RanCompT $ ffmap (Compose . gh . getCompose) . runRanCompT rak

instance (Functor f, FMonad mm) => FMonad (RanCompT f mm) where
    fpure gx = RanCompT $ \k -> fpure (Compose (fmap k gx))
    fjoin rr = RanCompT $ \k -> fjoin . ffmap (\(Compose r) -> runRanCompT r id) $ runRanCompT rr k

-- | A \"transformer\" version of 'CompLan', made out of composition @(\`Compose\` f) ∘ mm ∘ Lan f@.
newtype CompLanT f mm g a = CompLanT { runCompLanT :: mm (Lan f g) (f a) }

deriving instance (Functor f, FFunctor mm) => Functor (CompLanT f mm g)

instance (Functor f, FFunctor mm) => FFunctor (CompLanT f mm) where
    ffmap gh = CompLanT . ffmap (ffmap gh) . runCompLanT

instance (Functor f, FMonad mm) => FMonad (CompLanT f mm) where
    fpure gx = CompLanT . fpure . getCompose . toComposeLan $ fpure gx
    fjoin ll = CompLanT $ fjoin . ffmap (\(Lan t (CompLanT m)) -> fmap t m) . runCompLanT $ ll