{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

-- | This module explains theoretical backings of 'FStrong' and 'FStrongMonad'
--   type classes through examples.
module FStrongNonUniqueness where

import Data.Functor ((<&>))
import Data.Bifunctor (Bifunctor(..))

import Data.Functor.Day(Day(..))
import Data.Functor.Day.Curried

import FFunctor
import FStrong
import FMonad (FMonad (..))
import FStrong.Monad (FStrongMonad)

-- * Stamping action on functor and its relation to 'Curried'

newtype Stamp a h r = Stamp {unStamp :: h (r,a)}
  deriving (Functor, Foldable, Traversable)

-- ** @Stamp a h r@ is \"trifunctor\" on all three parameters.

instance FFunctor (Stamp a) where
  ffmap fg = Stamp . fg . unStamp

mapStamp :: Functor h => (a -> b) -> Stamp a h r -> Stamp b h r
mapStamp f = Stamp . fmap (second f) . unStamp

eps :: (a -> r, a) -> r
eps = uncurry ($)

runCurried' :: (Functor g) => Curried g h a -> (g ~> Stamp a h)
runCurried' (Curried gh) gr = Stamp $ gh ((,) <$> gr)

mkCurried' :: (Functor h) => (g ~> Stamp a h) -> Curried g h a
mkCurried' gh = Curried $ \gar -> eps <$> unStamp (gh gar)

unitStamp :: (Functor h) => Stamp () h ~> h
unitStamp = fmap fst . unStamp

unitStamp' :: (Functor h) => h ~> Stamp () h
unitStamp' = Stamp . fmap (,())

assocStamp :: (Functor h) => Stamp (a,b) h ~> Stamp a (Stamp b h)
assocStamp = Stamp . Stamp . fmap (\(x,(a,b)) -> ((x,a),b)) . unStamp

assocStamp' :: (Functor h) => Stamp a (Stamp b h) ~> Stamp (a,b) h
assocStamp' = Stamp . fmap (\((x,a),b) -> (x,(a,b))) . unStamp . unStamp


-- * @Hop@
--
-- 'Hop' is an alternative, equivalent formulation of 'FStrong', convenient to
-- analyze examples of 'FFunctor' instances with various 'FStrong' instances.

-- | Moves 'Stamp' out.
--
-- ==== Laws
-- 
-- @hop@ is a costrength on @FFunctor ff@ of an action @Stamp@ of types to @Functor@s.
--
-- @
-- -- Unit law
-- hop . ffmap unitStamp' = unitStamp'
-- -- Associativity law
-- hop . ffmap assocStamp' = assocStamp' . ffmap hop . hop
-- @
-- 
-- Moreover, @hop@ should be natural in both @a@ and @h@,
-- in addition to it is a natural transformation in the usual sense: natural in the last parameter @r@
-- for @hop :: ff (Stamp a h) r -> Stamp a (ff h) r@.
--
-- @
-- -- Naturality for the first parameter a
-- hop . ffmap (mapStamp β) = mapStamp β . hop
-- -- Naturality for the second parameter h
-- hop . ffmap (ffmap φ) = ffmap (ffmap φ) . hop
-- @
--
-- By parametricity, all of the three naturality conditions are
-- automatically safisfied for any @hop@ implemented in Haskell,
-- ignoring bottoms (@undefined@ etc.) and laziness-related feastures
-- like `seq`.  
class (FFunctor ff) => Hop ff where
  hop :: (Functor h) => ff (Stamp a h) ~> Stamp a (ff h)

-- | 'hop' can be defined in terms of 'mapCurried'
hopDefault :: (FStrong ff, Functor h) => ff (Stamp a h) ~> Stamp a (ff h)
hopDefault = runCurried' (mapCurried (mkCurried' id))

-- | 'mapCurried' can be defeind in terms of 'hop'.
--
-- Constructions 'hopDefault' and 'mapCurried' are inverses each other.
mapCurriedDefault ::
  (Hop ff, Functor g, Functor h) =>
  Curried g h ~> Curried (ff g) (ff h)
mapCurriedDefault gh = mkCurried' (hop . ffmap (runCurried' gh))

-- | 'fstrength' in terms of 'hop'.
fstrengthDefault ::
  (Hop ff, Functor g) =>
  Day (ff g) h ~> ff (Day g h)
fstrengthDefault (Day ffg h op) = fmap (uncurry op) . unStamp $ hop (ffmap (`stampDay` h) ffg)

stampDay :: g a -> h b -> Stamp b (Day g h) a
stampDay g h = Stamp $ Day g h (,)

-- * Examples with multiple or no Hop instances

-- ** Dup
--
-- @Dup@ is an example of @FFunctor@ with multiple possible @Hop@ instances,
-- equivalently multiple possible @FStrong@ instances.

newtype Dup f a = Dup { runDup :: f (f a)}
  deriving (Functor)

deriving instance Show (f (f a)) => Show (Dup f a)

instance FFunctor Dup where
  ffmap gh = Dup . fmap gh . gh . runDup

instance Hop Dup where
  hop = hop1

-- | There are two valid instances of @Hop Dup@
hop1, hop2 :: Functor h => Dup (Stamp a h) ~> Stamp a (Dup h)
hop1 (Dup shsh) = Stamp . Dup $ unStamp shsh <&> \(sh, a0) -> unStamp sh <&> \(x,_) -> (x,a0)
hop2 (Dup shsh) = Stamp . Dup $ unStamp shsh <&> \(sh, _)  -> unStamp sh <&> \(x,a1) -> (x,a1)

-- ** Free1
--
-- @Free1@ is another example of @FFunctor@ with multiple @Hop@ instances
-- (= @FStrong@ instances.)
--
-- Additionally, @Free1@ has an @FMonad@ instance. In the multiple @hop@ candidates,
-- 
-- - there is a @hop@ candidate **incompatible** with the @FMonad@ instance, and
-- - there are multiple **compatible** @hop@ candidates.
-- 
-- The existence of **incompatible** one shows the necessity of distinction between
-- pairs of instances @(FStrong mm, FMonad mm)@ those are compatible and those are not, 
-- motivating the class 'FStrongMonad' to state they are compatible.

-- | Free Bind (Bind = Monad sans pure)
data Free1 f a = Lift (f a) | Wrap1 (f (Free1 f a))
  deriving Functor

join1 :: Functor f => Free1 f (Free1 f a) -> Free1 f a
join1 (Lift fma) = Wrap1 fma
join1 (Wrap1 fmma) = Wrap1 (fmap join1 fmma)

instance FFunctor Free1 where
  ffmap gh (Lift ga) = Lift (gh ga)
  ffmap gh (Wrap1 gma) = Wrap1 (fmap (ffmap gh) (gh gma))

instance FMonad Free1 where
  fpure = Lift
  fbind k (Lift ga) = k ga
  fbind k (Wrap1 gma) = join1 $ k (fmap (fbind k) gma)

instance FStrong Free1 where
  fstrength = fstrengthDefault

instance Hop Free1 where
  hop = hopLast

instance FStrongMonad Free1

-- | "Take the last" hopping. This choice of @hop@ correponds to a @FStrong@ instance
--   compatible to the @FMonad Free1@ instance.
hopLast :: Functor h => Free1 (Stamp a h) ~> Stamp a (Free1 h)
hopLast (Lift sh) = Stamp . Lift $ unStamp sh
hopLast (Wrap1 shmx) = Stamp . Wrap1 $ unStamp shmx <&> \(mx, _) -> unStamp (hopLast mx)

-- | "Take the first" hopping. This choice of @hop@ correponds to a @FStrong@ instance
--   compatible to the @FMonad Free1@ instance.
hopFirst :: Functor h => Free1 (Stamp a h) ~> Stamp a (Free1 h)
hopFirst (Lift sh) = Stamp . Lift . unStamp $ sh
hopFirst (Wrap1 shmx) = Stamp . Wrap1 $ unStamp shmx <&> \(mx,a) -> go a mx
  where
    go :: Functor g => a -> Free1 (Stamp b g) x -> Free1 g (x,a)
    go a0 (Lift sg) = Lift . fmap (a0 <$) . unStamp $ sg
    go a0 (Wrap1 sgmx) = Wrap1 $ unStamp sgmx <&> \(mx, _) -> go a0 mx

-- | "Take the second if it has 2 or more depth, othewise take the first."
--
-- @hopSecond@ is an example for that a @FMonad mm@ can have
-- @FStrong mm@ instance that is incompatible with its @FMonad mm@ instance.
hopSecond :: Functor h => Free1 (Stamp a h) ~> Stamp a (Free1 h)
hopSecond (Lift sh) = Stamp . Lift . unStamp $ sh
hopSecond (Wrap1 shmx) = Stamp . Wrap1 $ unStamp shmx <&> \(mx,_) -> unStamp (hopFirst mx)

-- | Generalization to 'hopSecond' to infinite families of distinct @Hop@ instances.
hopNth :: Functor h => Int -> (Free1 (Stamp a h) ~> Stamp a (Free1 h))
hopNth n
  | n <= 0 = error ("Negative n:" ++ show n)
  | n == 1 = hopFirst
  | otherwise = \case
      Lift sh -> Stamp . Lift . unStamp $ sh
      Wrap1 shmx -> Stamp . Wrap1 $ unStamp shmx <&> \(mx,_) -> unStamp (hopFirst mx)
