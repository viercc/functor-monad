{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module Data.Functor.Day.Comonoid(Comonoidal(..), erase1, erase2) where

import Data.Functor.Day
import Data.Functor.Sum

-- | Comonoid with respect to Day convolution.
--
-- /Laws/:
-- 
-- > erase1 copure . coapply = id
-- > erase2 copure . coapply = id
-- > trans1 coapply . coapply = assoc . trans2 coapply . coapply 
class Functor f => Comonoidal f where
    copure :: f a -> a
    coapply :: f a -> Day f f a

-- | @erase1 tr = elim1 . trans1 (Identity . tr)@
erase1 :: Functor g => (forall a. f a -> a) -> Day f g c -> g c
erase1 tr fg = case fg of
    Day f g op -> op (tr f) <$> g

-- | @erase2 tr = elim2 . trans2 (Identity . tr)@
erase2 :: Functor f => (forall b. g b -> b) -> Day f g c -> f c
erase2 tr fg = case fg of
    Day f g op -> (\a -> op a (tr g)) <$> f

-- | @transBi t u = trans1 t . trans2 u = trans2 u . trans1 t@
transBi :: (forall x. f x -> f' x) -> (forall x. g x -> g' x) -> Day f g a -> Day f' g' a
transBi t u (Day f g op) = Day (t f) (u g) op

interchange :: Day (Day f f') (Day g g') x -> Day (Day f g) (Day f' g') x
interchange = disassoc . trans1 (assoc . trans2 swapped . disassoc) . assoc

instance Comonoidal ((,) a) where
    copure :: forall x. (a,x) -> x
    copure = snd

    coapply :: forall x. (a,x) -> Day ((,) a) ((,) a) x
    -- ~ forall x. (a,x) -> ∃b c. ((a,b), (a,c), b -> c -> x)
    -- ~ forall x. (a,x) -> (a,a, ∃b c.(b, c, b -> c -> x))
    -- ~ forall x. (a,x) -> (a,a,x)
    -- ~ a -> (a,a)
    coapply (a,x) = Day (a,()) (a,()) (\_ _ -> x)

instance Monoid m => Comonoidal ((->) m) where
    copure :: forall x. (m -> x) -> x
    copure = ($ mempty)

    coapply :: forall x. (m -> x) -> Day ((->) m) ((->) m) x
    -- ~ forall x. (m -> x) -> ∃b c. (m -> b, m -> c, b -> c -> x)
    -- ~ forall x. (m -> x) -> (m -> m -> x)
    -- ~ m -> m -> m
    coapply f = Day id id (\x y -> f (x <> y))

instance (Comonoidal f, Comonoidal g) => Comonoidal (Sum f g) where
    copure (InL f) = copure f
    copure (InR g) = copure g

    coapply (InL f) = transBi InL InL (coapply f)
    coapply (InR g) = transBi InR InR (coapply g)

instance (Comonoidal f, Comonoidal g) => Comonoidal (Day f g) where
    copure (Day f g op) = op (copure f) (copure g)
    coapply = interchange . transBi coapply coapply
