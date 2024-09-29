{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}

-- | Explain 'Control.Monad.Trail.Trail' monad in terms of adjoint functors
module TrailAsAdjunction(
  -- * Building blocks

  Const(..), Pair, Shape(..), Emptied(..), Y, Γ(..),

  mapPair, mapShape, mapEmptied, mapY, mapΓ,

  -- * Adjunctions
  -- $adjunction_diagrams

  adjunctPairShape,
  adjunctPairShape',
  adjunctShapeConst,
  adjunctShapeConst',
  adjunctConstEmptied,
  adjunctConstEmptied',
  adjunctΓY,
  adjunctΓY',

  -- * Monads and Comonads from these adjunctions

  J0(..), K1(..), J1(..), RR(..),

  -- * Examples
  --
  -- $doc_example

  R(..),

) where

import Data.Void
import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Const
import Control.Comonad
import Control.Monad (ap)
import Data.Coerce (coerce)

import FFunctor (FFunctor(..), type (~>))
import FMonad (FMonad (..))
import FComonad (FComonad (..))


{- $adjunction_diagrams

There is a chain of three adjunctions between @Type@ and @Functor@

>                    Type
>   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
>      |            ^          |            ^
>      |            |          |            |
> Pair |  -|  Shape | -| Const | -| Emptied | 
>      |            |          |            |
>      v            |          v            |
>   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
>                   Functor

And an adjunction between @Type^op@ and @Functor@

>       Type^op
>   ~~~~~~~~~~~~~~~~
>      ^      |
>      |      |
>    Γ |  -|  | Y
>      |      |
>      |      v
>   ~~~~~~~~~~~~~~~~
>      Functor

-}

{- $doc_example

'J0' and 'J1' turn an @FMonad mm@ to a @Monad@. The following table shows what is the
@Monad@ they make for each @FMonad@.

+-----------+-------------+--------------------+-------------------+------------+------------+
| @mm@      | @Compose m@ | @Precompose m@     | @Sum f@           | @Free@     | @FreeT' m@ |
+===========+=============+====================+===================+============+============+
| @'J0' mm@ | @m@         | @Identity@         | @Either (f Void)@ | @Identity@ | @m@        |
+-----------+-------------+--------------------+-------------------+------------+------------+
| @'J1' mm@ | @m@         | @Writer (Ap m ())@ | @Either (f ())@   | @[]@       | @ListT m@  |
+-----------+-------------+--------------------+-------------------+------------+------------+

'K1' takes an @FComonad ww@ and turns them a @Comonad@. 'RR' takes an @FComonad ww@ and turns
them a @Monad@, instead of @Comonad@.

+-----------+-------------+--------------------+-------------------+------------+---------------------+
| @ww@      | @Compose w@ | @Precompose w@     | @Product f@       | @Cofree@   | @Sum ff gg@         |
+===========+=============+====================+===================+============+=====================+
| @'K1' ww@ | @w@         | @Identity@         | @Env (f ())@      | @Identity@ | @K1 ff :+: K1 gg@   |
+-----------+-------------+--------------------+-------------------+------------+---------------------+
| @'RR' ww@ | @Co w@      | @R w@              | @Exp1 f Identity@ | @[]@       | ??                  |
+-----------+-------------+--------------------+-------------------+------------+---------------------+

Where

- 'Control.Monad.Co.Co' is a @Monad@ defined in "Control.Monad.Co" from kan-extensions package
- 'R' is a @Monad@ defined below
- 'Data.Functor.Exp.Exp1' is defined in "Data.Functor.Exp"

-}

-- * Building blocks

-- | @Pair :: Type -> Functor@
type Pair = (,)

mapPair :: (a -> b) -> (Pair a ~> Pair b)
mapPair = first

-- | Yoneda embedding
--
-- @Y :: Type^op -> Functor@
type Y = (->)

mapY :: (a -> b) -> (Y b ~> Y a)
mapY = flip (.)

-- | @Emptied :: Functor -> Type@
newtype Emptied f = Emptied { getEmptied :: f Void }

mapEmptied :: (f ~> g) -> Emptied f -> Emptied g
mapEmptied fg (Emptied f0) = Emptied (fg f0)

-- | @Shape :: Functor -> Type@
newtype Shape f = Shape { getShape :: f () }

mapShape :: (f ~> g) -> Shape f -> Shape g
mapShape fg (Shape f1) = Shape (fg f1)

-- | @Γ :: Functor -> Type^op@
newtype Γ f = Γ { getΓ :: forall x. f x -> x }

mapΓ :: (f ~> g) -> Γ g -> Γ f
mapΓ fg (Γ k) = Γ (k . fg)

-- * Adjunctions

adjunctPairShape :: (Pair a ~> f) -> (a -> Shape f)
adjunctPairShape h a = Shape (h (a,()))

adjunctPairShape' :: Functor f => (a -> Shape f) -> (Pair a ~> f)
adjunctPairShape' g (a,b) = b <$ getShape (g a)

adjunctShapeConst :: Functor f => (Shape f -> a) -> (f ~> Const a)
adjunctShapeConst h fb = Const $ h (Shape (() <$ fb))

adjunctShapeConst' :: (f ~> Const a) -> (Shape f -> a)
adjunctShapeConst' g (Shape f1) = getConst $ g f1

adjunctConstEmptied :: (Const a ~> f) -> a -> Emptied f
adjunctConstEmptied h a = Emptied (h (Const a))

adjunctConstEmptied' :: Functor f => (a -> Emptied f) -> (Const a ~> f)
adjunctConstEmptied' g (Const a) = vacuous $ getEmptied (g a)


-- | @adjunctΓY :: (Γ f `'Control.Category.Op'` a) -> (f ~> Y a)@
adjunctΓY :: (a -> Γ f) -> (f ~> Y a)
adjunctΓY h fb a = getΓ (h a) fb

-- | @adjunctΓY' :: (f ~> Y a) -> (Γ f `Control.Category.Op` a)@ 
adjunctΓY' :: (f ~> Y a) -> (a -> Γ f)
adjunctΓY' g a = Γ (\fb -> g fb a)

-- * Monads and Comonads from these adjunctions

-- | @J0 mm ~ Emptied ∘ mm ∘ Const@
newtype J0 mm a = J0 { runJ0 :: mm (Const a) Void }

instance FFunctor mm => Functor (J0 mm) where
  fmap f = J0 . ffmap (first f) . runJ0

instance FMonad mm => Applicative (J0 mm) where
  pure = J0 . fpure . Const
  (<*>) = ap

instance FMonad mm => Monad (J0 mm) where
  ma >>= k = J0 $ fbind (adjunctConstEmptied' (coerce . k)) (runJ0 ma)

-- | @K ww ~ Shape ∘ ww ∘ Const@ 
newtype K1 ww a = K1 { runK1 :: ww (Const a) () }

instance FFunctor ww => Functor (K1 ww) where
  fmap f = K1 . ffmap (first f) . runK1

instance FComonad ww => Comonad (K1 ww) where
  extract :: K1 ww a -> a
  extract = getConst . fextract . runK1

  extend :: (K1 ww a -> b) -> K1 ww a -> K1 ww b
  extend h = K1 . fextend (adjunctShapeConst (h . coerce)). runK1

-- | @J1 mm ~ Emptied ∘ mm ∘ Const@
--
-- Also, @J1 ~ 'Control.Monad.Trail.Trail'@
newtype J1 mm a = J1 { runJ1 :: mm (Pair a) () }

instance FFunctor mm => Functor (J1 mm) where
  fmap f = J1 . ffmap (first f) . runJ1

instance FMonad mm => Applicative (J1 mm) where
  pure = J1 . fpure . (, ())
  (<*>) = ap

instance FMonad mm => Monad (J1 mm) where
  ma >>= k = J1 $ fbind (adjunctPairShape' (coerce . k)) (runJ1 ma)

-- | @RR ww ~ Γ ∘ ww ∘ Y@
newtype RR ww a = RR { runRR :: Γ (ww (Y a)) }

instance FFunctor ww => Functor (RR ww) where
  fmap f = RR . mapΓ (ffmap (mapY f)) . runRR

instance FComonad ww => Applicative (RR ww) where
  pure a = RR $ Γ $ \wwk -> fextract wwk a
  (<*>) = ap

instance FComonad ww => Monad (RR ww) where
  ma >>= k = RR $ Γ $ \wwk -> getΓ (runRR ma) (fextend (adjunctΓY (runRR . k)) wwk)

-- | @RR ww@ specialized to @ww = Precompose w@
newtype R w a = R { runR :: forall r. (a -> w r) -> r }

instance Functor (R w) where
  fmap f rw = R $ \cont -> runR rw (cont . f)

instance Comonad w => Applicative (R w) where
  pure a = R $ \cont -> extract (cont a)
  (<*>) = ap

instance Comonad w => Monad (R w) where
  rw >>= k = R $ \cont -> runR rw (\a -> runR (k a) (duplicate . cont))