{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module FMonad
  ( type (~>),
    FFunctor (..),
    FMonad (..),
    fjoin
  )
where

import qualified Control.Applicative.Free as FreeAp
import qualified Control.Applicative.Free.Final as FreeApFinal
import Control.Applicative.Lift
import qualified Control.Applicative.Trans.FreeAp as FreeApT
import Control.Comonad (Comonad (..), (=>=))
import Control.Monad (join)
import qualified Control.Monad.Free as FreeM
import qualified Control.Monad.Free.Church as FreeMChurch
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.Functor.Compose
import Data.Functor.Day
import Data.Functor.Day.Comonoid
import Data.Functor.Day.Curried
import Data.Functor.Day.Extra (uncurried)
import Data.Functor.Flip1
import Data.Functor.Kan.Lan
import Data.Functor.Kan.Ran
import Data.Functor.Product
import Data.Functor.Sum
import FFunctor

import qualified Data.Bifunctor.Product as Bi
import qualified Data.Bifunctor.Product.Extra as Bi

-- | Monad on 'Functor's.
--
-- FMonad laws:
--
-- [fpure is natural in g]
--
--    For all @Functor g@, @Functor h@, and @n :: g ~> h@,
--
--    > ffmap n . fpure = fpure . n
--
-- [fjoin is natural in g]
--
--    For all @Functor g@, @Functor h@, and @n :: g ~> h@,
--
--    > ffmap n . fjoin = fjoin . ffmap (ffmap n)
--
-- [Left unit]
--
--    > fjoin . fpure = id
--
-- [Right unit]
--
--    > fjoin . fmap fpure = id
--
-- [Associativity]
--
--    > fjoin . fjoin = fjoin . ffmap fjoin
class FFunctor ff => FMonad ff where
  fpure :: (Functor g) => g ~> ff g
  fbind :: (Functor g, Functor h) => ff g a -> (g ~> ff h) -> ff h a

fjoin :: (FMonad ff, Functor g) => ff (ff g) ~> ff g
fjoin x = fbind x id

instance Functor f => FMonad (Sum f) where
  fpure = InR

  fbind (InL fa) _ = InL fa
  fbind (InR ga) k = k ga

instance (Functor f, forall a. Monoid (f a)) => FMonad (Product f) where
  fpure = Pair mempty
  fbind (Pair fa1 ga) k = case k ga of
    (Pair fa2 ha) -> Pair (fa1 <> fa2) ha

instance Monad f => FMonad (Compose f) where
  fpure = Compose . return
  fbind fg k = fjoin_ $ ffmap k fg
    where fjoin_ = Compose . join . fmap getCompose . getCompose

instance FMonad Lift where
  fpure = Other
  fbind (Pure a) _ = Pure a
  fbind (Other ga) k = k ga

instance FMonad FreeM.Free where
  fpure = FreeM.liftF
  fbind m k = FreeM.foldFree k m

instance FMonad FreeMChurch.F where
  fpure = FreeMChurch.liftF
  fbind m k = FreeMChurch.foldF k m

instance FMonad FreeAp.Ap where
  fpure = FreeAp.liftAp
  fbind m k = FreeAp.runAp k m

instance FMonad FreeApFinal.Ap where
  fpure = FreeApFinal.liftAp
  fbind m k = FreeApFinal.runAp k m

instance FMonad IdentityT where
  fpure = IdentityT
  fbind (IdentityT ga) k = k ga

instance FMonad (ReaderT e) where
  -- See the similarity between 'Compose' @((->) e)@

  -- return :: x -> (e -> x)
  fpure = ReaderT . return

  -- join :: (e -> e -> x) -> (e -> x)
  fbind m k = fjoin_ $ ffmap k m
    where
      fjoin_ = ReaderT . join . fmap runReaderT . runReaderT 

instance Monoid m => FMonad (WriterT m) where
  -- See the similarity between 'FlipCompose' @(Writer m)@

  -- fmap return :: f x -> f (Writer m x)
  fpure = WriterT . fmap (,mempty)

  -- fmap join :: f (Writer m (Writer m x)) -> f (Writer m x)
  fbind m k = fjoin_ $ ffmap k m
    where
      fjoin_ = WriterT . fmap (\((x, m1), m2) -> (x, m2 <> m1)) . runWriterT . runWriterT

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

  fbind m k = StateT . fjoin_ . fmap runStateT . runStateT $ ffmap k m
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

-- | @Ran w (Ran w f) ~ Ran ('Compose' w w) f@
instance (Comonad w) => FMonad (Ran w) where
  fpure ::
    forall f x.
    (Functor f) =>
    f x ->
    Ran w f x
  --       f x -> (forall b. (x -> w b) -> f b)
  fpure f = Ran $ \k -> fmap (extract . k) f

  fbind m t = fjoin_ $ ffmap t m
    where 
      --       (forall b c. (x -> w b) -> (b -> w c) -> f c) -> (forall d. (x -> w d) -> f d)
      fjoin_ rrf = Ran $ \k -> runRan (runRan rrf (duplicate . k)) id

-- | @Lan w (Lan w f) ~ Lan ('Compose' w w) f@
instance (Comonad w) => FMonad (Lan w) where
  fpure ::
    forall f x.
    (Functor f) =>
    f x ->
    Lan w f x
  --       f x -> exists b. (w b -> x, f b)
  fpure f = Lan extract f

  
  fbind m k = fjoin_ $ ffmap k m
    where
      --       (exists b. (w b -> x, exists c. (w c -> b, f c)) -> exists d. (w d -> x, f d)
      fjoin_ (Lan j1 (Lan j2 f)) = Lan (j2 =>= j1) f

instance (Applicative f) => FMonad (Day f) where
  fpure :: g ~> Day f g
  fpure = day (pure id)

  {-
     day :: f (a -> b) -> g a -> Day f g b
  -}
  
  fbind m k = trans1 dap . assoc . trans2 k $ m

{-
   dap :: Day f f ~> f
   trans1 dap :: Day (Day f f) g ~> Day f g
   assoc               :: Day f (Day f g) ~> Day (Day f f) g
-}

instance Comonoid f => FMonad (Curried f) where
  fpure :: Functor g => g a -> Curried f g a
  fpure g = Curried $ \f -> extract f <$> g

  fbind m k = Curried $ \f -> runCurried (uncurried (ffmap k m)) (coapply f)

instance FMonad (FreeApT.ApT f) where
  fpure = FreeApT.liftT
  fbind m k = FreeApT.fjoinApTLeft $ ffmap k m

instance Applicative g => FMonad (Flip1 FreeApT.ApT g) where
  fpure = Flip1 . FreeApT.liftF
  fbind m k = Flip1 . FreeApT.foldApT unFlip1 FreeApT.liftT . unFlip1 $ ffmap k m

instance (FMonad ff, FMonad gg) => FMonad (Bi.Product ff gg) where
  fpure h = Bi.Pair (fpure h) (fpure h)
  fbind (Bi.Pair ff gg) k = Bi.Pair (fbind ff (Bi.proj1 . k)) (fbind gg (Bi.proj2 . k))
