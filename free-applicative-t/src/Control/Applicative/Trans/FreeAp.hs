{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | 'Applicative' functor transformers, like monad transformers, for free.
module Control.Applicative.Trans.FreeAp (
  ApT (..),
  toFree,
  fromFree,
  transApT,
  hoistApT,
  liftF,
  liftT,
  appendApT,
  foldApT,
  foldApT_,
  fjoinApTLeft,
  fjoinApTRight,
  ApIx (..),
  fromIx, indices,
  reconstruct
) where

import Control.Applicative
import qualified Control.Applicative.Free as Free
import Data.Foldable (toList)
import Data.Functor.Identity
import Data.Traversable (mapAccumL)

import qualified GHC.Arr as Arr
import GHC.Stack (HasCallStack)

import Data.Functor.Classes

{- | @'ApT' f@ is a \"free\" \"applicative transformer\", in the same sense
  @'Control.Monad.Trans.Free.FreeT' f@ is a free monad transformer.

  ==== \"Applicative transformer\"

  Being an \"applicative transformer\" means these two things:

  * Applying @ApT f@ to an applicative functor @g@ constructs a new applicative
    functor @ApT f g@.

  * Using 'liftT', you can lift an action of @g@ to the action of @ApT f g@.

      > liftT :: g x -> ApT f g x

      'liftT' is an applicative transformation. In other words, @liftT@ preserves
      'pure' and @'<*>'@:

      > liftT (pure x) = pure x
      > liftT (x <*> y) = liftT x <*> liftT y

  ==== \"Free\" applicative transformer

  It's the \"free\" applicative transformer. It means @ApT f g@ is the special, the most universal
  one among various applicative functors which can lift @f@ and @g@ into them.

  * @ApT f g@ has a way to lift any value of @f a@ into an action of @ApT f g a@.

      > liftF :: (Applicative g) => f a -> ApT f g a

      Because @ApT f g@ is also an applicative transformer on @g@, it has a way to lift @g@ too.

      > liftT :: g x -> ApT f g x

  * Suppose another applicative functor @h@ is capable of lifting both @f@ and @g@ to @h@.

      > fh :: f a -> h a
      > gh :: g a -> h a

      @ApT f g@ is the universal applicative among them. There's 'foldApT' to construct
      the applicative transformation from @ApT f g@ to @h@, without losing how to lift @f@ and @g@.

      > foldApT :: forall f g h x. Applicative h => (forall a. f a -> h a) -> (forall a. g a -> h a) -> ApT f g x -> h x
      >
      > foldApT fh gh :: forall x. ApT f g x -> h x
      >
      > foldApT fh gh . liftF = fh
      > foldApT fh gh . liftT = gh

  * @ApT f g@ contains no extra data that are not from lifting @f@ and/or @g@ then combining them together
    by @Applicative@ operation '<*>'.

      It means any applicative transformation @run :: forall a. ApT f g a -> h a@ which satisfies @run . liftF = fh@ and @run . liftT = gh@
      is equivalent to @foldApT fh gh@.
-}
data ApT f g x
  = PureT (g x)
  | forall a b c. ApT (a -> b -> c -> x) (g a) (f b) (ApT f g c)

instance Functor g => Functor (ApT f g) where
  fmap h (PureT gx) = PureT $ fmap h gx
  fmap h (ApT x ga fb rc) = ApT (\a b c -> h (x a b c)) ga fb rc

  x <$ PureT gx = PureT (x <$ gx)
  x <$ ApT _ ga fb rc = ApT (\_ _ _ -> x) ga fb rc

instance Applicative g => Applicative (ApT f g) where
  pure = PureT . pure
  PureT gx <*> PureT gy = PureT (gx <*> gy)
  PureT gx <*> ApT y ga fb rc = ApT (\ ~(x, a) b c -> x (y a b c)) (liftA2 (,) gx ga) fb rc
  ApT x ga fb rc <*> rest = ApT (\a b ~(c, y) -> x a b c y) ga fb (liftA2 (,) rc rest)

  PureT gx *> PureT gy = PureT (gx *> gy)
  PureT gx *> ApT y ga fb rc = ApT y (gx *> ga) fb rc
  ApT _ ga fb rc *> rest = ApT (\_ _ y -> y) ga fb (rc *> rest)

  PureT gx <* PureT gy = PureT (gx <* gy)
  PureT gx <* ApT _ ga fb rc = ApT (\x _ _ -> x) (gx <* ga) fb rc
  ApT x ga fb rc <* rest = ApT x ga fb (rc <* rest)

-- | When the base applicative is 'Identity', @ApT f Identity@ is the free applicative 'Free.Ap'.
toFree :: ApT f Identity a -> Free.Ap f a
toFree = toFreeAux id

toFreeAux :: (a -> b) -> ApT f Identity a -> Free.Ap f b
toFreeAux k (PureT (Identity a)) = Free.Pure (k a)
toFreeAux k (ApT x (Identity a) fb rc) = Free.Ap fb (toFreeAux (\c b -> k (x a b c)) rc)

-- | Inverse of @toFree@.
fromFree :: Free.Ap f a -> ApT f Identity a
fromFree (Free.Pure a) = PureT (Identity a)
fromFree (Free.Ap fb rest) = ApT flip (Identity id) fb (fromFree rest)

{- | Lift an applicative transformation @(forall a. g a -> g' a)@ to
  an applicative transformation @(forall b. ApT f g b -> ApT f g' b)@.
-}
hoistApT :: (forall a. g a -> g' a) -> ApT f g b -> ApT f g' b
hoistApT phi (PureT gx) = PureT (phi gx)
hoistApT phi (ApT x ga fb rc) = ApT x (phi ga) fb (hoistApT phi rc)

{- | Lift any natural transformation @(forall a. f a -> f' a)@ to
  an applicative transformation @(forall b. ApT f g b -> ApT f' g b)@.
-}
transApT :: (forall a. f a -> f' a) -> ApT f g b -> ApT f' g b
transApT _ (PureT gx) = PureT gx
transApT phi (ApT x ga fb rc) = ApT x ga (phi fb) (transApT phi rc)

-- | Lift an applicative action @g x@ to @ApT f g x@
liftT :: g x -> ApT f g x
liftT = PureT

-- | Lift an uninterpreted action @f x@ to @ApT f g x@
liftF :: Applicative g => f x -> ApT f g x
liftF fx = ApT (\_ x _ -> x) (pure ()) fx (pure ())

{- | Equivalent to the following definition, but is faster and doesn't require @Applicative g@ constraint.

  @appendApT x prefix fb postfix = x \<$\> prefix \<*\> liftF fb \<*\> postfix@
-}
appendApT :: (a -> b -> c -> x) -> ApT f g a -> f b -> ApT f g c -> ApT f g x
appendApT x prefix fb postfix = case prefix of
  PureT ga -> ApT x ga fb postfix
  ApT a ga' fb' prefix' -> ApT (\a' b' ~(c', b, c) -> x (a a' b' c') b c) ga' fb' (appendApT (,,) prefix' fb postfix)

{- | Interpret @ApT f g@ into an applicative @h@.

  When @g@ is an @Applicative@ and @gh :: forall a. g a -> h a@ is an applicative transformation,
  @'foldApT' fh gh@ is an applicative transformation too.

  @foldApT@ satisfy the following equations with 'liftF' and 'liftT'.

  > foldApT fh gh . liftF = fh
  > foldApT fh gh . liftT = gh
-}
foldApT :: forall f g h x. Applicative h => (forall a. f a -> h a) -> (forall a. g a -> h a) -> ApT f g x -> h x
foldApT f2h g2h = go
 where
  go :: forall y. ApT f g y -> h y
  go (PureT gx) = g2h gx
  go (ApT x ga fb rc) = liftA3 x (g2h ga) (f2h fb) (go rc)

{- | Perform a monoidal analysis over @ApT f g@ value.

  This is equivalent to use @foldApT@ with the applicative @'Control.Applicative.Const' m@,
  except @m@ doesn't need to be a @Monoid@ but just a @Semigroup@.
-}
foldApT_ :: forall f g m x. Semigroup m => (forall a. f a -> m) -> (forall a. g a -> m) -> ApT f g x -> m
foldApT_ f2m g2m = go
 where
  go :: forall y. ApT f g y -> m
  go (PureT gx) = g2m gx
  go (ApT _ ga fb rc) = g2m ga <> f2m fb <> go rc

-- | Collapsing @ApT@ nested left-to-right.
fjoinApTLeft :: forall f g x. ApT f (ApT f g) x -> ApT f g x
fjoinApTLeft = go
 where
  go :: forall y. ApT f (ApT f g) y -> ApT f g y
  go (PureT inner) = inner
  go (ApT y inner fb rest) = appendApT y inner fb (go rest)

-- | Collapsing @ApT@ nested right-to-left.
fjoinApTRight :: Applicative g => ApT (ApT f g) g x -> ApT f g x
fjoinApTRight = foldApT id liftT

-------------
instance (Foldable f, Foldable g) => Foldable (ApT f g) where
  foldMap f (PureT gx) = foldMap f gx
  foldMap f (ApT x ga fb rc) =
    foldFor ga $ \a ->
      foldFor fb $ \b ->
        foldFor rc $ \c -> f (x a b c)
  length = go 1
   where
    go :: forall any. Int -> ApT f g any -> Int
    go 0 _ = 0
    go n (PureT gx) = n * length gx
    go n (ApT _ f g r) = go (length f * length g * n) r
  null (PureT gx) = null gx
  null (ApT _ ga fb rc) = null ga || null fb || null rc

foldFor :: (Foldable f, Monoid m) => f a -> (a -> m) -> m
foldFor = flip foldMap

{- | Printable value indicating \"shape\" of @ApT f g@ functor.
  If you forget the data of elements from @ApT f g x@, and leave numbers indicating
  which index these data was in the @ApT f g@, that is @ApIx f g@.

    >>> xFn = (\a b c -> if a then show b else c)
    >>> x = ApT xFn [True, False] [10, 20] (PureT ["Moo"])
    >>> toList x
    ["10", "20", "Moo", "Moo"]

A value of type @ApIx [] []@ corresponding to @x@ represents it was made from the three lists
of length @2,2,1@ each. In @ApIx f g@ values, instead of having the original contents, they contain
@Int@ values to conveniently calculate the indices of the value in @toList x@.

    >>> indices x
    ApIx [0, 2] [0, 1] (PureIx [0])

-}
data ApIx f g where
  PureIx :: g Int -> ApIx f g
  ApIx :: g Int -> f Int -> ApIx f g -> ApIx f g

deriving stock instance (Show (f Int), Show (g Int)) => Show (ApIx f g)
deriving stock instance (Eq (f Int), Eq (g Int)) => Eq (ApIx f g)
deriving stock instance (Ord (f Int), Ord (g Int)) => Ord (ApIx f g)

space :: ShowS
space = showChar ' '

-- | Turn a shape value @ApIx f g@ to the actual @ApT f g Int@ value
--   containing indices.
fromIx :: Functor g => ApIx f g -> ApT f g Int
fromIx (PureIx gi) = PureT gi
fromIx (ApIx gi fj r) = ApT (\i j k -> i + j + k) gi fj (fromIx r)

lengthIx :: (Foldable f, Foldable g) => ApIx f g -> Int
lengthIx = go 1
 where
  go 0 _ = 0
  go n (PureIx g) = n * length g
  go n (ApIx g f r) = go (n * length g * length f) r

indicesF :: (Traversable f) => f a -> f Int
indicesF = snd . mapAccumL (\n _ -> n `seq` (n + 1, n)) 0

-- | Extract only a shape from @ApT f g x@ and make it @ApIx f g@.
indices :: forall f g x. (Traversable f, Traversable g) => ApT f g x -> ApIx f g
indices u
  | null u    = ripoff u
  | otherwise = snd (go u)
  where
    ripoff :: ApT f g z -> ApIx f g
    ripoff (PureT gx) = PureIx (0 <$ gx)
    ripoff (ApT _ ga fb rc) = ApIx (0 <$ ga) (0 <$ fb) (ripoff rc)
    
    go :: forall y. ApT f g y -> (Int, ApIx f g)
    go (PureT gx) = (length gx, PureIx (indicesF gx))
    go (ApT _ ga fb rc) =
      let lenG = length ga
          lenF = length fb
          (lenR, rk) = go rc
          gi' = (lenF * lenR *) <$> indicesF ga
          fj' = (lenR *) <$> indicesF fb
          len = lenG * lenF * lenR
      in len `seq` (len, ApIx gi' fj' rk)

-- | Construct an @ApT f g x@ value from a shape @ApIx f g@ and a list of values.
--
--   For any @u :: ApT f g x@, the following property holds.
--
--   > reconstruct (indices u) (toList u) == u
--   
--   @reconstruct shape xs@ raises 'error' if the length of list @xs@ does not match
--   the length calculated from @shape@.
reconstruct :: (HasCallStack, Foldable f, Foldable g, Functor g) => ApIx f g -> [x] -> ApT f g x
reconstruct shape xs
  | length xs == n = (xsArr Arr.!) <$> fromIx shape
  | otherwise = error "Wrong number of elements in the table"
  where
    n = lengthIx shape
    xsArr = Arr.listArray (0, n - 1) xs

instance (Traversable f, Traversable g) => Traversable (ApT f g) where
  traverse f u = fmap (reconstruct (indices u)) (traverse f (toList u))

instance (Traversable f, Show (f Int), Traversable g, Show (g Int), Show a) => Show (ApT f g a) where
  showsPrec = showsPrec1

instance (Traversable f, Show (f Int), Traversable g, Show (g Int)) => Show1 (ApT f g) where
  liftShowsPrec showsPrecX showListX p u =
    showParen (p > 10) $ ("reconstruct " ++) . showsPrec 11 (indices u) . space . liftShowsPrec showsPrecX showListX 11 (toList u)

instance (Eq1 f, Eq1 g, Eq a) => Eq (ApT f g a) where
  (==) = eq1

instance (Eq1 f, Eq1 g) => Eq1 (ApT f g) where
  liftEq eq (PureT g1) (PureT g2) = liftEq eq g1 g2
  liftEq eq (ApT x1 g1 f1 r1) (ApT x2 g2 f2 r2)
    | emptyEq g1 g2 = boringEq f1 f2 && boringEqApT r1 r2
    | emptyEq f1 f2 = boringEq g1 g2 && boringEqApT r1 r2
    | otherwise =
        liftEqFor g1 g2 $ \a1 a2 ->
          liftEqFor f1 f2 $ \b1 b2 ->
            liftEqFor r1 r2 $ \c1 c2 ->
              eq (x1 a1 b1 c1) (x2 a2 b2 c2)
  liftEq _ _ _ = False

instance (Ord1 f, Ord1 g, Ord a) => Ord (ApT f g a) where
  compare = compare1

instance (Ord1 f, Ord1 g) => Ord1 (ApT f g) where
  liftCompare cmp (PureT g1) (PureT g2) = liftCompare cmp g1 g2
  liftCompare cmp (ApT x1 g1 f1 r1) (ApT x2 g2 f2 r2)
    | emptyEq g1 g2 = boringCompare f1 f2 <> boringCompareApT r1 r2
    | emptyEq f1 f2 = boringCompare g1 g2 <> boringCompareApT r1 r2
    | otherwise =
        liftCompareFor g1 g2 $ \a1 a2 ->
          liftCompareFor f1 f2 $ \b1 b2 ->
            liftCompareFor r1 r2 $ \c1 c2 ->
              cmp (x1 a1 b1 c1) (x2 a2 b2 c2)
  liftCompare _ PureT{} ApT{} = LT
  liftCompare _ ApT{} PureT{} = GT

-- | Order shuffled 'liftEq'
liftEqFor :: Eq1 f => f a -> f b -> (a -> b -> Bool) -> Bool
liftEqFor f1 f2 eq = liftEq eq f1 f2

-- | Order shuffled 'liftCompare'
liftCompareFor :: Ord1 f => f a -> f b -> (a -> b -> Ordering) -> Ordering
liftCompareFor f1 f2 cmp = liftCompare cmp f1 f2

emptyEq, boringEq :: Eq1 f => f a -> f b -> Bool
emptyEq = liftEq (\_ _ -> False)
boringEq = liftEq (\_ _ -> True)

boringCompare :: Ord1 f => f a -> f b -> Ordering
boringCompare = liftCompare (\_ _ -> EQ)

boringEqApT :: (Eq1 f, Eq1 g) => ApT f g a -> ApT f g b -> Bool
boringEqApT (PureT g1) (PureT g2) = boringEq g1 g2
boringEqApT (ApT _ g1 f1 r1) (ApT _ g2 f2 r2) = boringEq g1 g2 && boringEq f1 f2 && boringEqApT r1 r2
boringEqApT _ _ = False

boringCompareApT :: (Ord1 f, Ord1 g) => ApT f g a -> ApT f g b -> Ordering
boringCompareApT (PureT g1) (PureT g2) = boringCompare g1 g2
boringCompareApT (ApT _ g1 f1 r1) (ApT _ g2 f2 r2) = boringCompare g1 g2 <> boringCompare f1 f2 <> boringCompareApT r1 r2
boringCompareApT PureT{} ApT{} = LT
boringCompareApT ApT{} PureT{} = GT
