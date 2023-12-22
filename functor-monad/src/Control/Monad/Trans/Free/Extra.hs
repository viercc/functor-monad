{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Various utility functions on 'FreeT'
module Control.Monad.Trans.Free.Extra where

import Control.Arrow ((>>>))
import Control.Monad.Trans.Free
import FFunctor (type (~>))

ffmapFreeF :: forall f g a. (f ~> g) -> FreeF f a ~> FreeF g a
ffmapFreeF _ (Pure a) = Pure a
ffmapFreeF fg (Free fb) = Free (fg fb)

transFreeT_ :: forall f g m. (Functor g, Functor m) => (f ~> g) -> FreeT f m ~> FreeT g m
transFreeT_ fg =
  let go = FreeT . fmap (fmap go . ffmapFreeF fg) . runFreeT in go

traverseFreeT_ ::
  (Traversable f, Traversable m, Applicative g) =>
  (a -> g b) ->
  FreeT f m a ->
  g (FreeT f m b)
traverseFreeT_ f = go
  where
    go (FreeT x) = FreeT <$> traverse goF x
    goF (Pure a) = Pure <$> f a
    goF (Free fmx) = Free <$> traverse go fmx

inr :: Functor m => m ~> FreeT f m
inr = FreeT . fmap Pure

inl :: (Functor f, Monad m) => f ~> FreeT f m
inl = FreeT . return . Free . fmap return

eitherFreeT_ :: Monad n => (f ~> n) -> (m ~> n) -> (FreeT f m ~> n)
eitherFreeT_ nt1 nt2 = go
  where
    go ma =
      do
        v <- nt2 (runFreeT ma)
        case v of
          Pure a -> return a
          Free fm -> nt1 fm >>= go

caseFreeF :: (a -> r) -> (f b -> r) -> FreeF f a b -> r
caseFreeF pureCase freeCase freef = case freef of
  Pure a -> pureCase a
  Free fb -> freeCase fb

fbindFreeT_ :: forall f m n a. (Functor f, Functor m, Functor n) => (m ~> FreeT f n) -> FreeT f m a -> FreeT f n a
fbindFreeT_ k = outer
  where
    outer :: FreeT f m a -> FreeT f n a
    outer = runFreeT >>> k >>> inner

    inner :: FreeT f n (FreeF f a (FreeT f m a)) -> FreeT f n a
    inner =
      -- T m (F a (T m a))
      runFreeT
        >>> fmap (caseFreeF (caseFreeF Pure (Free . fmap outer)) (Free . fmap inner))
        >>> FreeT

fconcatFreeT_ :: forall f m. (Functor f, Functor m) => FreeT f (FreeT f m) ~> FreeT f m
fconcatFreeT_ = fbindFreeT_ id
