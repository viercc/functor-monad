{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Functor.Day.Comonoid (
  -- * Comonoid type class
  Comonoid (..), erase1, erase2, duplicateDefault, extendDefault, dayToCompose,
  -- * Re-export
  Comonad(..)
  ) where

import Data.Functor.Day
import Data.Functor.Sum ( Sum(..) )
import Data.Functor.Identity (Identity(..))

import Control.Comonad (Comonad(..))
import Control.Comonad.Trans.Identity (IdentityT(..))
import Control.Comonad.Env (EnvT(..) )
import Control.Comonad.Traced (TracedT(..) )

-- | Comonoid with respect to Day convolution.
--
-- ==== Laws
-- 
-- 'coapply' must satisfy the following equations. Here, @erase1@ and @erase2@
-- are defined using 'extract' method inherited from 'Comonad'.
-- 
-- @
-- 'erase1' . 'coapply' = id
-- 'erase2' . 'coapply' = id
-- 'trans1' 'coapply' . 'coapply' = 'assoc' . 'trans2' 'coapply' . 'coapply'
-- @
-- 
-- Furthermore, 'duplicateDefault' derived from @coapply@ must be equivalent to 'duplicate'
-- inherited from 'Comonad'.
-- 
-- @
-- 'duplicateDefault' = 'dayToCompose' . coapply
--                  = 'duplicate'
-- @
--
-- ==== Examples
-- 
-- Env comonad, or @(,) e@, is an instance of @Comonoid@.
--
-- 
-- > instance Comonoid ((,) e) where
-- >   coapply :: forall x. (e, x) -> Day ((,) e) ((,) e) x
-- >   -- ~ forall x. (e,x) -> ∃b c. ((e,b), (e,c), b -> c -> x)
-- >   -- ~ forall x. (e,x) -> (e,e, ∃b c.(b, c, b -> c -> x))
-- >   -- ~ forall x. (e,x) -> (e,e,x)
-- >   -- ~ e -> (e,e)
-- >   coapply (e, x) = Day (e, ()) (e, ()) (\_ _ -> x)
--
-- Traced comonad, or @((->) m)@, is another example.
-- 
-- > instance Monoid m => Comonoid ((->) m) where
-- >   coapply :: forall x. (m -> x) -> Day ((->) m) ((->) m) x
-- >   -- ~ forall x. (m -> x) -> ∃b c. (m -> b, m -> c, b -> c -> x)
-- >   -- ~ forall x. (m -> x) -> (m -> m -> x)
-- >   -- ~ m -> m -> m
-- >   coapply f = Day id id (\x y -> f (x <> y))
--
-- ==== Non-example
--
-- Unlike @Env@ or @Traced@, 'Control.Comonad.Store.Store' comonad can't be an instance of @Comonoid@.
-- The law requires any lawful @Comonoid f@ to satisfy the following property.
-- 
-- * For any value of @f x@, 'coapply' doesn't change the \"shape\" of it. Precisely, for any value @fx :: f x@,
--   the following equation is true.
--
--     > () <$ coapply fx ≡ Day (() <$ fx) (() <$ fx) (\_ _ -> ())@
-- 
-- Therefore, any lawful @Comonoid (Store s)@ must satisfy the following equation:
--
-- > coapply (store u s0) ≡ Day (store u s0) (store u s0) (\_ _ -> ())
-- >   where u = const () :: s -> ()
-- 
-- But it's incompatible with another requirement that @duplicateDefault@ must be equivalent to @duplicate@ of
-- the @Comonad (Store s)@ instance.
--
-- > duplicateDefault (store u s0) = store (const (store u s0)) s0
-- > duplicate        (store u s0) = store (\s1 -> store u s1)  s0

class Comonad f => Comonoid f where
  coapply :: f a -> Day f f a

-- | Every 'Comonoid' is a 'Comonad'.
duplicateDefault :: Comonoid f => f a -> f (f a)
duplicateDefault = dayToCompose . coapply

-- | Every 'Comonoid' is a 'Comonad'.
extendDefault :: Comonoid f => (f a -> b) -> f a -> f b
extendDefault t = fmap t . duplicateDefault


-- | @'Day' f g@ can be turned into a composition of @f@ and @g@.
dayToCompose :: (Functor f, Functor g) => Day f g a -> f (g a)
dayToCompose (Day fb fc op) = fmap (\b -> fmap (op b) fc) fb

-- | @erase1 = elim1 . trans1 (Identity . extract)@
erase1 :: (Comonad f, Functor g) => Day f g c -> g c
erase1 fg = case fg of
  Day f g op -> op (extract f) <$> g

-- | @erase2 = elim2 . trans2 (Identity . extract)@
erase2 :: (Functor f, Comonad g) => Day f g c -> f c
erase2 fg = case fg of
  Day f g op -> (\a -> op a (extract g)) <$> f

-- | @transBi t u = trans1 t . trans2 u = trans2 u . trans1 t@
transBi :: (forall x. f x -> f' x) -> (forall x. g x -> g' x) -> Day f g a -> Day f' g' a
transBi t u (Day f g op) = Day (t f) (u g) op

interchange :: Day (Day f f') (Day g g') x -> Day (Day f g) (Day f' g') x
-- interchange = disassoc . trans1 (assoc . trans2 swapped . disassoc) . assoc
interchange (Day (Day fa fb ab_x) (Day gc gd cd_y) xy_r) =
  Day (Day fa gc (,)) (Day fb gd (,)) (\(a,c) (b,d) -> xy_r (ab_x a b) (cd_y c d))

instance Comonoid Identity where
  coapply (Identity a) = Day (Identity ()) (Identity ()) (\_ _ -> a)

instance Comonoid ((,) e) where
  coapply :: forall x. (e, x) -> Day ((,) e) ((,) e) x
  coapply (e, x) = Day (e, ()) (e, ()) (\_ _ -> x)

instance Monoid m => Comonoid ((->) m) where
  coapply :: forall x. (m -> x) -> Day ((->) m) ((->) m) x
  coapply f = Day id id (\x y -> f (x <> y))

instance (Comonoid f, Comonoid g) => Comonoid (Sum f g) where
  coapply (InL f) = transBi InL InL (coapply f)
  coapply (InR g) = transBi InR InR (coapply g)

instance (Comonoid f, Comonoid g) => Comonoid (Day f g) where
  coapply = interchange . transBi coapply coapply

instance (Comonoid f) => Comonoid (IdentityT f) where
  coapply (IdentityT fx) = transBi IdentityT IdentityT (coapply fx)

instance (Comonoid f) => Comonoid (EnvT e f) where
  coapply (EnvT e fx) = transBi (EnvT e) (EnvT e) (coapply fx)

instance (Monoid m, Comonoid f) => Comonoid (TracedT m f) where
  coapply (TracedT ft) = case coapply ft of
    Day fa fb op -> Day (TracedT ((,) <$> fa)) (TracedT ((,) <$> fb)) (\(a, m1) (b, m2) -> op a b (m1 <> m2))