{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-- | This module explains theoretical backings of 'FStrong' and 'FStrongMonad'
--   type classes through examples.
module FStrongNonUniqueness where

import Data.Functor ((<&>))
import Data.Bifunctor (Bifunctor(..))

import Data.Functor.Day(Day(..))
import Data.Functor.Day.Curried

import FFunctor
import FStrong
import FMonad (FMonad (..), fjoin)
import FStrong.Monad (FStrongMonad)
import Data.Kind (Type)
import Data.Functor.Identity
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

-- * Stamping action on functor and its relation to 'Curried'

newtype Stamp a h r = Stamp {unStamp :: h (r,a)}
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (h (r,a))) => Show (Stamp a h r)

-- ** @Stamp a h r@ is \"trifunctor\" on all three parameters.

instance FFunctor (Stamp a) where
  ffmap fg = Stamp . fg . unStamp

mapStamp :: Functor h => (a -> b) -> Stamp a h r -> Stamp b h r
mapStamp f = Stamp . fmap (second f) . unStamp

eps :: (a -> r, a) -> r
eps = uncurry ($)

-- | @Curried g h a@ is isomorphic to natural transformation @g ~> Stamp a h@.
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
-- automatically satisfied for any @hop@ implemented in Haskell,
-- ignoring bottoms (@undefined@ etc.) and laziness-related features
-- like `seq`.  
--
-- ==== Compatibility laws between @FMonad@
-- 
-- For a @Hop ff@ instance, if there is also an @FMonad ff@ instance, one can consider if they
-- are compatible in the same way @FStrong ff@ and @FMonad ff@ forming @FStrongMonad ff@.
--
-- Compatibility condition with @FMonad@, using @hop@, can be written as below:
--
-- /Compatibility with @fpure@/:
--
--     @
--     'hop' . 'fpure' = 'ffmap' fpure
--         :: Stamp a h ~> Stamp a (ff h)
--     @
--
-- /Compatibility with @fjoin@/:
--
--     @
--     'hop' . 'fjoin'
--       = ffmap fjoin . hop . ffmap hop
--         :: ff (ff (Stamp a h)) ~> Stamp a (ff (ff h)) 
--     @

class (FFunctor ff) => Hop ff where
  hop :: (Functor h) => ff (Stamp a h) ~> Stamp a (ff h)

-- | 'hop' can be defined in terms of 'mapCurried'
hopDefault :: (FStrong ff, Functor h) => ff (Stamp a h) ~> Stamp a (ff h)
hopDefault = runCurried' (mapCurried (mkCurried' id))

-- | 'mapCurried' can be defined in terms of 'hop'.
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

-- | There are two valid instances of @Hop Dup@.
--
-- >>> e = Dup $ Stamp [ (Stamp [('a', 10)], 1), (Stamp [('b', 20), ('c', 21)], 2)] :: Dup (Stamp Int []) Char
-- >>> hop1 e
-- Stamp {unStamp = Dup {runDup = [[('a',1)],[('b',2),('c',2)]]}}
-- >>> hop2 e
-- Stamp {unStamp = Dup {runDup = [[('a',10)],[('b',20),('c',21)]]}}
hop1, hop2 :: Functor h => Dup (Stamp a h) ~> Stamp a (Dup h)
hop1 (Dup shsh) = Stamp . Dup $ unStamp shsh <&> \(sh, a0) -> unStamp sh <&> \(x,_) -> (x,a0)
hop2 (Dup shsh) = Stamp . Dup $ unStamp shsh <&> \(sh, _)  -> unStamp sh <&> \(x,a1) -> (x,a1)

-- ** Par
--
-- @Par@ is an example of @FFunctor@ such that *no* 'Hop' instances can be made.

type Par :: (Type -> Type) -> Type -> Type
newtype Par f a = Par a
  deriving (Show, Functor)

instance FFunctor Par where
  ffmap _ (Par a) = Par a

-- | Ignoring @Par@ and @Stamp@ newtypes, the type required to
--   implement 'hop' for @Par@ is
--
-- @
-- hop' :: forall a r. r -> (a, r)
-- @
--
-- which is impossible to implement without using an 'undefined' value,
-- like how 'hopParUndefined' below is implemented.
hopParUndefined :: forall h a r. Functor h => Par (Stamp a h) r -> Stamp a (Par h) r
hopParUndefined (Par r0) = Stamp $ Par (r0, undefined :: a)

-- ** 'Poke'
--
-- 'Poke' is another example of @FFunctor@ with no possible 'Hop' instances,
-- but by a different reason.
--
-- @Hop 'Par'@ was impossible because of its @hop@ cannot be implemented
-- (without using @undefined@). Unlike that, for some concrete type @S@,
-- an expression satisfying the type of @hop@ for @Poke S@ can be writte,
-- but *no* such expressions satisfy @Hop@ law.

newtype Poke s f a = Poke { poke :: (a -> s) -> f s }
  deriving Functor

instance FFunctor (Poke s) where
  ffmap gh (Poke x) = Poke (gh . x)

-- | @Poke s@ is also an example of @FMonad@ without any @Hop@ (thus @FStrong@)
-- instance.
instance FMonad (Poke s) where
  fpure ga = Poke $ \k -> k <$> ga
  fbind next pga = Poke $ \k -> next (pga `poke` k) `poke` id

data S1 = S1
newtype S2 = S2 Bool

-- | @Poke s@ can have a lawful @Hop@ instance if and only if
--   @s@ is a singleton type.
instance Hop (Poke S1) where
  hop = hopPoke1

hopPoke1 :: forall a h r. Functor h
    => Poke S1 (Stamp a h) r -> Stamp a (Poke S1 h) r
---- ≅ ((r -> S1) -> h (S1,a)) -> ((a,r) -> S1) -> h S1
---    ^^^^^^^^^^^^^^^^^^^^^^^    ^^^^^^^^^^^^^
---    | poke p              |    | k         |
hopPoke1 p = Stamp $ Poke $ \_ -> S1 <$ unStamp (poke p (const S1))

hopPoke2Violating :: forall a h r. Functor h
    => Poke S2 (Stamp a h) r -> Stamp a (Poke S2 h) r
---- ≅ ((r -> S2) -> h (S2,a)) -> ((a,r) -> S2) -> h S2
---    ^^^^^^^^^^^^^^^^^^^^^^^    ^^^^^^^^^^^^^
---    | poke p              |    | k         |
hopPoke2Violating p = Stamp $ Poke $ \k -> {- ??? -}
  -- The expected type for the hole is @h S2@.
  -- Because @h@ is a polymorphic @Functor@,
  -- the only way to make a value of @h _@ is to
  -- apply @fmap@ to existing one.

  -- The only way to get one value here is to invoke
  -- 
  -- @
  -- unStamp . poke p :: (r -> S2) -> h (S2,a)
  -- @
  --
  -- . Therefore, the hole ??? must be shaped

    post k <$> unStamp (poke p (pre k))
  
  -- for a pair of functions @pre k@, @post k@.
  --
  -- Furthermore, @pre@ and @post@ cannot depend on @p@,
  -- since the types of @pre, post@ does not mention @h@
  -- and @Functor h@ alone does not give any data to distinguish
  -- between values of @h _@.
  where
    -- Since @a,r@ are both rigid type variables,
    -- there is no way to call @k@ arguemnt,
    -- nor inspect @r0 :: r@ to change the returning @S2@ value depending
    -- on it.
    --
    -- Therefore, the only possible implementation is to return any
    -- constant S2 value.
    pre :: ((r,a) -> S2) -> (r -> S2)
    pre k = \r0 -> s2

    s2 :: S2
    s2 = S2 False

    -- By similar arugument to @pre@,
    -- the only possible implementation is to return
    -- a @S2@ value depending on only @s@, ignoring
    -- @k, a1@.
    post :: ((r,a) -> S2) -> (S2,a) -> S2
    post k = \(s,a1) -> g s

    g :: S2 -> S2
    g = id

{-

@hop = hopS2Violating@ breaks @Hop@ law, regardless of how @s2@ and @g@ are chosen.
In fact, it does not satisfy the unit law

    hop . ffmap unitStamp' = unitStamp'

. To show it fails, let

    x :: Poke S2 Identity ()
    -- ≅ (() -> S2) -> S2
    x = Poke $ \k -> Identity (k ())

and evaluate both sides of the unit law on @x@.

    (RHS) = unitStamp' x
    = Stamp $ fmap ((),) x
    = Stamp $ Poke $ \k -> Identity (k ((),()))

    (Lhs) = hop . ffmap unitStamp'
    = hop $ Poke $ \k -> Stamp (Identity (k (), ()))
    = Stamp $ Poke $ \k ->
        post k <$> Identity (pre k (), ())
    = Stamp $ Poke $ \k -> Identity (g s1)

Unwrapping newtypes and equality of function,

    g s1 = k ((), ())

must hold for all @k :: ((), ()) -> S2@. But this is impossible,
because RHS can take two distinct values @S2 False, S2 True@
depending on @k@, while LHS is a constant determined by choice of @g@ and @s1@.

By the same argument, if any lawful @hop@ for @Poke S@ existed,
any value of @S@ must be equal to @g s1 :: S@ determined by @hop@.
Therefore, such @S@ must be isomorphic to the unit type @()@.
-}

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

retract1 :: Monad f => Free1 f a -> f a
retract1 (Lift fa) = fa
retract1 (Wrap1 fma) = fma >>= retract1

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

-- | "Take the last" hopping. This choice of @hop@ corresponds to a @FStrong@ instance
--   compatible to the @FMonad Free1@ instance.
hopLast :: Functor h => Free1 (Stamp a h) ~> Stamp a (Free1 h)
hopLast (Lift sh) = Stamp . Lift $ unStamp sh
hopLast (Wrap1 shmx) = Stamp . Wrap1 $ unStamp shmx <&> \(mx, _) -> unStamp (hopLast mx)

-- | "Take the first" hopping. This choice of @hop@ corresponds to a @FStrong@ instance
--   compatible to the @FMonad Free1@ instance.
hopFirst :: Functor h => Free1 (Stamp a h) ~> Stamp a (Free1 h)
hopFirst (Lift sh) = Stamp . Lift . unStamp $ sh
hopFirst (Wrap1 shmx) = Stamp . Wrap1 $ unStamp shmx <&> \(mx,a) -> go a mx
  where
    go :: Functor g => a -> Free1 (Stamp b g) x -> Free1 g (x,a)
    go a0 (Lift sg) = Lift . fmap (a0 <$) . unStamp $ sg
    go a0 (Wrap1 sgmx) = Wrap1 $ unStamp sgmx <&> \(mx, _) -> go a0 mx

-- | "Take the second if it has 2 or more depth, otherwise take the first."
--
-- @hopSecond@ is an example for that a @FMonad mm@ can have
-- @FStrong mm@ instance that is incompatible with its @FMonad mm@ instance.
hopSecond :: Functor h => Free1 (Stamp a h) ~> Stamp a (Free1 h)
hopSecond (Lift sh) = Stamp . Lift . unStamp $ sh
hopSecond (Wrap1 shmx) = Stamp . Wrap1 $ unStamp shmx <&> \(mx,_) -> unStamp (hopFirst mx)

-- | Generalization to 'hopSecond' to infinite families of distinct @Hop@ instances.
hopNth :: Functor h => Int -> (Free1 (Stamp a h) ~> Stamp a (Free1 h))
hopNth n
  | n <= 0 = error ("Non-positive n:" ++ show n)
  | n == 1 = hopFirst
  | otherwise = \case
      Lift sh -> Stamp . Lift . unStamp $ sh
      Wrap1 shmx -> Stamp . Wrap1 $ unStamp shmx <&> \(mx,_) -> unStamp (hopNth (n-1) mx)

-- | @Free1 ((,) a) b@ is isomorphic to @(NonEmpty a, b)@.
--
-- Also, its @fjoin@ behaves like join of @NonEmpty (NonEmpty a)@:
--
-- > Free1 (Free1 ((,) a)) ≅ Free1 ((,) (NonEmpty a)) ≅ (,) (NonEmpty (NonEmpty a))
--
-- >>> xss = (0 :| [1,2]) :| [ 3 :| [4], 5 :| [] ] :: NonEmpty (NonEmpty Int)
-- >>> xss' = ffmap nonEmptyToFree1 $ nonEmptyToFree1 (xss, ())
-- >>> xs = fjoin xss'
-- >>> free1ToNonEmpty xs
-- (0 :| [1,2,3,4,5],())
--
-- 'hop' acts as a way to pick one element from @NonEmpty a@.
--
-- >>> ffmap retract1 $ hopFirst (ffmap pairToStamp xs)
-- Stamp {unStamp = Identity ((),0)}
-- >>> ffmap retract1 $ hopLast (ffmap pairToStamp xs)
-- Stamp {unStamp = Identity ((),5)}
-- >>> ffmap retract1 $ hopSecond (ffmap pairToStamp xs)
-- Stamp {unStamp = Identity ((),1)}
-- >>> ffmap retract1 $ hopNth 3 (ffmap pairToStamp xs)
-- Stamp {unStamp = Identity ((),2)}
--
-- This is also a counterexample to the compatibility between @hopSecond@ and
-- @FMonad@.
-- 
-- >>> xss'' = ffmap (ffmap pairToStamp) xss' :: Free1 (Free1 (Stamp Int Identity)) ()
-- >>> ffmap retract1 $ hopSecond . fjoin $ xss''
-- Stamp {unStamp = Identity ((),1)}
-- >>> ffmap retract1 $ ffmap fjoin . hopSecond . ffmap hopSecond $ xss''
-- Stamp {unStamp = Identity ((),4)}
free1ToNonEmpty :: Free1 ((,) a) b -> (NonEmpty a, b)
free1ToNonEmpty (Lift (a,b)) = (NE.singleton a, b)
free1ToNonEmpty (Wrap1 (a,rest)) = case free1ToNonEmpty rest of
  ~(as, b) -> (NE.cons a as, b)

nonEmptyToFree1 :: (NonEmpty a, b) -> Free1 ((,) a) b
nonEmptyToFree1 (a0 :| as, b) = go a0 as
  where
    go a1 [] = Lift (a1, b)
    go a1 (a2 : as') = Wrap1 (a1, go a2 as')

-- | @(,) a ≅ Stamp a Identity@
pairToStamp :: (,) a ~> Stamp a Identity
pairToStamp (a,b) = Stamp (Identity (b,a))

stampToPair :: Stamp a Identity ~> (,) a
stampToPair (Stamp (Identity (b,a))) = (a,b)
