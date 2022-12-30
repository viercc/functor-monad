{-# LANGUAGE DeriveTraversable #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Functor.Day.Extra where

import Data.Functor.Day
import Data.Functor.Classes

import Control.Applicative.Free

emptyEq, boringEq :: Eq1 f => f a -> f b -> Bool
emptyEq = liftEq (\_ _ -> False)
boringEq = liftEq (\_ _ -> True)

-- | Argument shuffled @liftEq@
eqFor :: Eq1 f => f a -> f b -> (a -> b -> Bool) -> Bool
eqFor f1 f2 eq = liftEq eq f1 f2

instance (Eq1 f, Eq1 g) => Eq1 (Day f g) where
    liftEq eq (Day f1 g1 op1) (Day f2 g2 op2)
      | emptyEq f1 f2 = boringEq g1 g2
      | otherwise     =
          eqFor f1 f2 $ \a1 a2 ->
            eqFor g1 g2 $ \b1 b2 ->
              eq (op1 a1 b1) (op2 a2 b2)

instance (Eq1 f) => Eq1 (Ap f) where
    liftEq eq (Pure a1) (Pure a2) = eq a1 a2
    liftEq eq (Ap f1 r1) (Ap f2 r2)
      | emptyEq f1 f2 = boringEqAp r1 r2
      | otherwise     =
          eqFor f1 f2 $ \a1 a2 ->
            eqFor r1 r2 $ \k1 k2 ->
              eq (k1 a1) (k2 a2)
    liftEq _ _ _ = False

-- | boringEq for Ap but efficient
boringEqAp :: Eq1 f => Ap f a -> Ap f b -> Bool
boringEqAp (Pure _) (Pure _) = True
boringEqAp (Ap f1 r1) (Ap f2 r2) = boringEq f1 f2 && boringEqAp r1 r2
boringEqAp _ _ = False

instance (Eq1 f, Eq a) => Eq (Ap f a) where
    (==) = eq1

-- Example:

data V2 a = V2 a a
  deriving (Eq, Functor, Foldable, Traversable)

instance Eq1 V2 where
    liftEq eq (V2 a1 a2) (V2 b1 b2) = eq a1 b1 && eq a2 b2

y1, y2 :: V2 Int
y1 = V2 0 1
y2 = V2 3 4

x1, x2, x3 :: [Bool]
x1 = [True, False]
x2 = [False, True]
x3 = [True]

d1, d1', d2, d2', d2'', d3, d3' :: Day [] V2 Int

-- d1 == d1'
d1 = Day x1 y1 (\b n -> if b then n + 1 else n - 1)
d1' = Day x2 y1 (\b n -> if b then n - 1 else n + 1)

-- d1 /= d2, d2 == d2' == d2''
d2 = Day x1 y2 (\b n -> if b then n else 0)
d2' = Day x2 y2 (\b n -> if b then 0 else n)
d2'' = Day x1 y1 (\b n -> if b then (n + 3) else 0)

-- d3 /= d3
d3 = Day x1 y1 (\_ _ -> 100)
d3' = Day x3 y1 (\_ _ -> 100)
