{-# LANGUAGE
  StandaloneKindSignatures,
  DerivingVia,
  DerivingStrategies,
  DeriveFunctor,
  StandaloneDeriving,
  RankNTypes,
  ScopedTypeVariables,
  InstanceSigs,
  TypeOperators,
  TupleSections,
  QuantifiedConstraints
#-}
module Main(main) where

import Data.Kind ( Type )
import Control.Monad.Trans.Class
import qualified Control.Monad.Trans.Free as Original

import Data.Monoid (Ap(..))

import FMonad.FreeT
import Control.Monad.Trail

{-

This example is inspired by a question raised at r/haskell (in fact, it inspired me to make
this package itself!)

ListT instances and -XDerivingVia: https://www.reddit.com/r/haskell/comments/i76yx2/listt_instances_and_xderivingvia/

> how can we derive @Monad@, @Alternative@, @Monoid@.. instances for @ListT@? 

-}

type    ListT :: (Type -> Type) -> (Type -> Type)
newtype ListT m a = ListT { runListT :: Original.FreeT ((,) a) m () }
    deriving stock (Eq, Ord, Show, Read)
    deriving (Functor, Applicative, Monad)
        via (Trail (FreeT' m))
    deriving (Semigroup, Monoid)
        via (Ap (FreeT ((,) a) m) ())

-- MonadTrans is specific to ListT
instance MonadTrans ListT where
  lift ma = ListT $ lift ma >>= \a -> Original.liftF (a, ())

-- For test:
forEach :: Monad m => ListT m a -> (a -> m ()) -> m ()
forEach as f = Original.iterT (\(a, m) -> f a >> m) . runListT $ as

test1, test2, test3 :: ListT IO Int
test1 = lift (putStrLn "SideEffect: A") >> mempty
test2 = lift (putStrLn "SideEffect: B") >> pure 1
test3 = lift (putStrLn "SideEffect: C") >> (pure 2 <> pure 3)

main :: IO ()
main = forEach test print
  where test = (test1 <> test2 <> test3) >>= \n -> pure 100 <> pure n
