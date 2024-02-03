{- | Exponentiation of a @Functor@ by a @Functor@.

For reference:

Powers of polynomial monads by David Spivak <https://topos.site/blog/2023/09/powers-of-polynomial-monads/>

-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
module Data.Functor.Exp where

import FFunctor
import GHC.Generics ((:*:)(..))
import Control.Monad (ap)
import Control.Comonad
import Control.Applicative
import FMonad
import FStrong
import Data.Functor.Day (Day(..))

newtype Exp1 f g a = Exp1 { unExp1 :: forall r. f r -> (a -> r) -> g r }
    deriving Functor

type (:^:) f g = Exp1 g f

toExp1 :: forall f g h. Functor g => ((f :*: g) ~> h) -> (g ~> Exp1 f h)
toExp1 fg2h gx = Exp1 (\fr xr -> fg2h (fr :*: fmap xr gx))

fromExp1 :: forall f g h. (g ~> Exp1 f h) -> ((f :*: g) ~> h)
fromExp1 g2fh (fx :*: gx) = unExp1 (g2fh gx) fx id

evalExp1 :: (f :*: Exp1 f g) ~> g
evalExp1 = fromExp1 id

coevalExp1 :: Functor g => g ~> Exp1 f (f :*: g)
coevalExp1 = toExp1 id

fromExp1' :: Functor f => Exp1 f g b -> f a -> g (Either a b)
fromExp1' e fa = unExp1 e (Left <$> fa) Right

toExp1' :: Functor g => (forall a. f a -> g (Either a b)) -> Exp1 f g b
toExp1' fg = Exp1 $ \fr br -> either id br <$> fg fr

instance (Functor f, Monad g) => Applicative (Exp1 f g) where
  pure a = Exp1 $ \_ ar -> pure (ar a)
  (<*>) = ap

instance (Functor f, Monad g) => Monad (Exp1 f g) where
  ma >>= k = Exp1 $ \fr br ->
    fromExp1' ma fr >>= \case
      Left r -> pure r
      Right a -> unExp1 (k a) fr br

-- | Equivalent to @'Data.Monoid.Alt' (Exp1 f g) a@
instance (Comonad f, Monad g) => Semigroup (Exp1 f g a) where
  (<>) = (<|>)

-- | Equivalent to @'Data.Monoid.Alt' (Exp1 f g) a@
instance (Comonad f, Monad g) => Monoid (Exp1 f g a) where
  mempty = empty

instance (Comonad f, Monad g) => Alternative (Exp1 f g) where
  empty = Exp1 $ \fr _ -> pure (extract fr)
  m1 <|> m2 = Exp1 $ \fr ar ->
    fromExp1' m1 (duplicate fr) >>= \case
      Left fr' -> unExp1 m2 fr' ar
      Right a  -> pure (ar a)


instance FFunctor (Exp1 f) where
  ffmap gh (Exp1 e) = Exp1 $ \fr ar -> gh (e fr ar) 

-- | @g ~ Exp1 Proxy g@; @Exp1 f (Exp1 f g) ~ Exp1 (f :*: f) g@
instance Functor f => FMonad (Exp1 f) where
  fpure gx = Exp1 $ \_ br -> br <$> gx
  fbind k fgx = Exp1 $ \fr yr ->
    unExp1 (k (fromExp1' fgx fr)) fr (either id yr)

instance Functor f => FStrong (Exp1 f) where
  fstrength (Day mb hc op) =
    Exp1 $ \fr ar ->
      let op' (Left r) _ = r
          op' (Right b) c = ar (op b c)
      in Day (fromExp1' mb fr) hc op'
