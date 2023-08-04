{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module FMonad.Instances.Trans where

import {-# SOURCE #-} FMonad
import FFunctor.Instances.Trans()

import Control.Applicative.Lift
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad (join)

instance FMonad Lift where
  fpure = Other
  fbind _ (Pure a)   = Pure a
  fbind k (Other ga) = k ga

instance FMonad IdentityT where
  fpure = IdentityT
  fbind k = k . runIdentityT

instance FMonad (ReaderT e) where
  -- See the similarity between 'Compose' @((->) e)@

  -- return :: x -> (e -> x)
  fpure = ReaderT . return

  -- join :: (e -> e -> x) -> (e -> x)
  fbind k = ReaderT . (>>= runReaderT . k) . runReaderT

instance Monoid m => FMonad (WriterT m) where
  -- See the similarity between 'FlipCompose' @(Writer m)@

  -- fmap return :: f x -> f (Writer m x)
  fpure = WriterT . fmap (,mempty)

  -- fmap join :: f (Writer m (Writer m x)) -> f (Writer m x)
  fbind k = WriterT . fmap (\((x, m1), m2) -> (x, m2 <> m1)) . runWriterT . runWriterT . ffmap k

{-

If everything is unwrapped, FMonad @(StateT s)@ is

  fpure :: forall f. Functor f => f x -> s -> f (x, s)
  fjoin :: forall f. Functor f => (s -> s -> f ((x, s), s)) -> s -> f (x, s)

And if this type was generic in @s@ without any constraint like @Monoid s@,
the only possible implementations are

  -- fpure is uniquely:
  fpure fx s = (,s) <$> fx

  -- fjoin is one of the following three candidates
  fjoin1 stst s = (\((x,_),_) -> (x,s)) <$> stst s s
  fjoin2 stst s = (\((x,_),s) -> (x,s)) <$> stst s s
  fjoin3 stst s = (\((x,s),_) -> (x,s)) <$> stst s s

But none of them satisfy the FMonad law.

  (fjoin1 . fpure) st
    = fjoin1 $ \s1 s2 -> (,s1) <$> st s2
    = \s -> (\((x,_),_) -> (x,s)) <$> ((,s) <$> st s)
    = \s -> (\(x,_) -> (x,s)) <$> st s
    /= st
  (fjoin2 . fpure) st
    = fjoin2 $ \s1 s2 -> (,s1) <$> st s2
    = \s -> (\((x,_),s') -> (x,s')) <$> ((,s) <$> st s)
    = \s -> (\(x,_) -> (x,s)) <$> st s
    /= st
  (fjoin3 . ffmap fpure) st
    = fjoin2 $ \s1 s2 -> fmap (fmap (,s2)) . st s1
    = \s -> ((\((x,s'),_) -> (x,s')) . fmap (,s)) <$> st s
    = \s -> (\(x,_) -> (x,s)) <$> st s
    /= st

So the lawful @FMonad (StateT s)@ will utilize some structure
on @s@.

One way would be seeing StateT as the composision of Reader s and
Writer s:

  StateT s m ~ Reader s ∘ m ∘ Writer s
    where (∘) = Compose

By this way

  StateT s (StateT s m) ~ Reader s ∘ Reader s ∘ m ∘ Writer s ∘ Writer s

And you can collapse the nesting by applying @join@ for @Reader s ∘ Reader s@
and @Writer s ∘ Writer s@. To do so, it will need @Monoid s@ for @Monad (Writer s)@.

-}

instance Monoid s => FMonad (StateT s) where
  -- Note that this is different to @lift@ in 'MonadTrans',
  -- whilst having similar type and actually equal in
  -- several other 'FMonad' instances.
  --
  -- See the discussion below.
  fpure fa = StateT $ \_ -> (,mempty) <$> fa

  fbind k = StateT . fjoin_ . fmap runStateT . runStateT . ffmap k
    where
      fjoin_ :: forall f a. (Functor f) => (s -> s -> f ((a, s), s)) -> s -> f (a, s)
      fjoin_ = fmap (fmap joinWriter) . joinReader
        where
          joinReader :: forall x. (s -> s -> x) -> s -> x
          joinReader = join

          joinWriter :: forall x. ((x, s), s) -> (x, s)
          joinWriter ((a, s1), s2) = (a, s2 <> s1)

{-

Note [About FMonad (StateT s) instance]

@fpure@ has a similar (Functor instead of Monad) type signature
with 'lift', but due to the different laws expected on them,
they aren't necessarily same.

@lift@ for @StateT s@ must be, by the 'MonadTrans' laws,
the one currently used. And this is not because the parameter @s@
is generic, so it applies if we have @Monoid s =>@ constraints like
the above instance.

One way to have @lift = fpure@ here is requiring @s@ to be a type with
group operations, @Monoid@ + @inv@ for inverse operator,
instead of just being a monoid.

> fpure fa = StateT $ \s -> (,s) <$> fa
> fjoin = StateT . fjoin_ . fmap runStateT . runStateT
>   where fjoin_ mma s = fmap (fmap (joinGroup s)) $ joinReader mma s
>         joinReader = join
>         joinGroup s ((x,s1),s2) = (x, s2 <> inv s <> s1)

-}
