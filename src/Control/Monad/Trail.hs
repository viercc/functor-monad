{-# LANGUAGE
  QuantifiedConstraints,
  DerivingVia,
  DerivingStrategies,
  DeriveTraversable,
  StandaloneDeriving,
  
  RankNTypes,
  ScopedTypeVariables,
  
  InstanceSigs,
  TypeOperators,
  TupleSections
#-}
module Control.Monad.Trail(Trail(..), Trail'(..), Stepstone(..)) where

import Control.Monad (ap)
import Data.Bifunctor

import FMonad

newtype Trail mm a = Trail { runTrail :: mm ((,) a) () }

instance (FFunctor mm) => Functor (Trail mm) where
    fmap f = Trail . ffmap (first f) . runTrail
      -- f :: a -> b
      -- first f :: forall c. (a, c) -> (b, c)

instance (FMonad mm) => Applicative (Trail mm) where
    pure a = Trail $ fpure (a, ())
    (<*>) = ap

instance (FMonad mm) => Monad (Trail mm) where
    ma >>= k = join_ (fmap k ma)
      where
        join_ = Trail . fjoin . ffmap (plug . first runTrail) . runTrail

plug :: forall f x. Functor f => (f (), x) -> f x
plug (f_,a) = a <$ f_

{-

Is it really lawful?

Preparation:

I'll use the following aliases:
  wrap = Trail
  unwrap = runTrail
  pf = plug . first unwrap

Using these aliases:
  return = wrap . fpure . (, ())
  join_  = wrap . fjoin . ffmap pf . unwrap

Also, for any natural transformation `n :: f ~> g`,
  Lemma [plugnat]
  plug . first n :: (f (), b) -> g b
   = \(f_, b) -> b <$ n f_
     -- (b <$) = fmap (const b), and fmap commutes with n
   = \(f_, b) -> n (b <$ f_)
   = n . plug

Note that they are all natural transformations:
* ffmap _
* fpure
* fjoin

(1) Left unit:

join_ . return
 = wrap . fjoin . ffmap pf . unwrap . wrap . fpure . (, ())
 = wrap . fjoin . ffmap pf . fpure . (, ())
   -- naturality of fpure
 = wrap . fjoin . fpure . pf . (, ())
                          ^^^^^^^^^^^
   {
     pf . (, ())
      = plug . first unwrap . (, ())
      = (() <$) . unwrap
      = fmap (const () :: () -> ()) . unwrap
      = fmap id . unwrap
      = unwrap
   }
 = wrap . fjoin . fpure . unwrap
   -- FMonad law
 = wrap . id . unwrap
 = id

(2) Right unit:

join_ . fmap return
 = wrap . fjoin . ffmap pf . unwrap .
   wrap . ffmap (first return) . unwrap
 = wrap . fjoin . ffmap pf . ffmap (first return) . unwrap
   -- FFunctor law
 = wrap . fjoin . ffmap (pf . first return) . unwrap
                         ^^^^^^^^^^^^^^^^^
   {
     pf . first return
      = plug . first unwrap . first (wrap . fpure . (,()))
      = plug . first (fpure . (,()))
      = plug . first fpure . first (,())
        -- [plugnat]
      = fpure . plug . first (,())
      = fpure . plug . (\(a,b) -> ((a,()), b))
      = fpure . (\(a,b) -> b <$ (a, ()))
      = fpure . (\(a,b) -> (a,b))
      = fpure
   }
 = wrap . fjoin . ffmap fpure . unwrap
   -- FMonad law
 = wrap . id . unwrap
 = id

(3) Associativity:

join_ . join_
 = wrap . fjoin . ffmap pf . unwrap .
   wrap . fjoin . ffmap pf . unwrap
 = wrap . fjoin . ffmap pf . fjoin . ffmap pf . unwrap
   -- naturality of fjoin
 = wrap . fjoin . fjoin . ffmap (ffmap pf) . ffmap pf . unwrap
 = wrap . fjoin . fjoin . ffmap (ffmap pf . pf) . unwrap

join_ . fmap join_
 = wrap . fjoin . ffmap pf . unwrap .
   wrap . ffmap (first (wrap . fjoin . ffmap pf . unwrap)) . unwrap
 = wrap . fjoin . ffmap pf .
          ffmap (first (wrap . fjoin . ffmap pf . unwrap)) . unwrap
 = wrap . fjoin .
     ffmap (pf . first (wrap . fjoin . ffmap pf . unwrap)) . unwrap
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   {
     pf . first (wrap . fjoin . ffmap pf . unwrap) 
      = plug . first unwrap . first (wrap . fjoin . ffmap pf . unwrap)
      = plug . first (fjoin . ffmap pf . unwrap)
      = plug . first (fjoin . ffmap pf) . first unwrap
        -- [plugnat]
      = fjoin . ffmap pf . plug . first unwrap
      = fjoin . ffmap pf . pf
   }
 = wrap . fjoin . ffmap (fjoin . ffmap pf . pf) . unwrap
 = wrap . fjoin . ffmap fjoin . ffmap (ffmap pf . f) . unwrap
   -- FMonad law
 = wrap . fjoin . fjoin . ffmap (ffmap pf . pf) . unwrap
 = join_ . join_

-}


data Stepstone s a r = Stepstone (s -> r) a
    deriving (Functor)

instance Bifunctor (Stepstone s) where
  first f (Stepstone leg a) = Stepstone leg (f a)
  second = fmap
  bimap f g (Stepstone leg a) = Stepstone (g . leg) (f a)

-- | @'Trail' mm ~ Trail' mm ()@
newtype Trail' mm s a = Trail' { runTrail' :: mm (Stepstone s a) s }

leap :: Functor f => Stepstone s (f s) x -> f x
leap (Stepstone leg fs) = fmap leg fs

pureStep :: a -> Stepstone s a s
pureStep = Stepstone id

instance (FFunctor mm) => Functor (Trail' mm s) where
  fmap f = Trail' . ffmap (first f) . runTrail'

instance (FMonad mm) => Applicative (Trail' mm s) where
  pure a = Trail' $ fpure (pureStep a)
  (<*>) = ap

instance (FMonad mm) => Monad (Trail' mm s) where
  ma >>= k = join_ (fmap k ma)
      where
        join_ = Trail' . fjoin . ffmap (leap . first runTrail') . runTrail'

{-

Examples:

> Trail' mm s

- @mm = ComposePost m@
  
  Trail' (ComposePost m) s a
    ~ ComposePost (Stepstone s a) s
    ~ m (Stepstone s a s)
    ~ m (a, s -> s)
    ~ WriterT (Endo s) m a

- @mm = ComposePre m@

  Trail' (ComposePre m) s a
    ~ ComposePre m (Stepstone s a) s
    ~ Stepstone s a (m s)
    ~ (a, s -> m s)
    ~ Writer (Endo (Kleisli m) s) a

- @mm = Free@

  Trail' Free s a
    ~ Free (Stepstone s a) s
    ~ μr. s + (s -> r, a)

  data T s a = End s | Step (s -> T s a) a

  pure a = Step a End
  join (End s) = End s
  join (Step f (End s)) = join (f s)
  join (Step f (Step a g)) = Step (\s -> join (Step f (g s))) a

- @mm = Sum f@

  Trail' (Sum f) s a
    ~ Sum f (Stepstone s a) s
    ~ f s + (s -> s, a)
  
  data T f s a = End (f s) | Step (s -> s) a
  pure a = Step id
  join (End fs) = End fs
  join (Step f (End fs)) = f <$> fs
  join (Step f (Step g a)) = Step (f . g) a

- @mm = Day f@

  Trail' (Day f) s a
    ~ Day f (Stepstone s a) s
    ~ ∃x y. (f x, Stepstone s a y, x -> y -> s)
    ~ ∃x y. (f x, s -> y, a, x -> y -> s)
    ~ ∃x. (f x, a, x -> s -> s)
    ~ (f (s -> s), a) 
    ~ Writer (Ap f (Endo s)) a

- @mm = FreeT' m@

  Trail' (FreeT' m) s a
    ~ FreeT (Stepstone s a) m s
    ~ m (s + (s -> FreeT (Stepstone s a) m s, a))

  newtype T m s a = T { runT :: m (Either s (s -> T m s a, a)) }

  inaction s = T $ pure (Left s)
  pure a = T $ pure (Right (inaction, a))

  join tt = T $ runT tt >>= \case
    Left s -> pure $ Left s
    Right (k, t) -> runT t >>= \case
      Left s -> runT (join (k s))
      Right (l, a) ->
        let kl s = join $ T $ pure (Right (k, ))

-}