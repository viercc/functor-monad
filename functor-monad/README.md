# functor-monad: Monads on category of Functors

This package provides `FFunctor` and `FMonad`,
each corresponds to `Functor` and `Monad` but is higher-order.

|      | a Functor `f`   | a FFunctor `ff` |
|----|----|----|
| Takes | `a :: Type` | `g :: Type -> Type`, `Functor g` |
| Makes | `f a :: Type` | `ff g :: Type -> Type`, `Functor (ff g)` |
| method | `fmap :: (a -> b) -> f a -> f b` | `ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g ~> ff h)` |

|      | a Monad `m`   | a FMonad `mm` |
|----|----|----|
| Superclass | Functor | FFunctor |
| method | `return = pure :: a -> m a` | `fpure :: (Functor g) => g ~> mm g` |
|        | `(>>=) :: m a -> (a -> m b) -> m b` | -- |
|        | `join :: m (m a) -> m a` | `fjoin :: (Functor g) => mm (mm g) ~> mm g` |

See also: https://viercc.github.io/blog/posts/2020-08-23-fmonad.html

## Motivational examples

Many types in [base] and popolar libraries like [transformers] have a parameter expecting a `Functor`.
For exmple:

```haskell
-- From "base", Data.Functor.Sum
data Sum f g x = InL (f x) | InR (g x)
instance (Functor f, Functor g) => Functor (Sum f g)

-- From "transformers", Control.Monad.Trans.Reader
newtype ReaderT r m x = ReaderT { runReaderT :: r -> m x }
instance (Functor m) => Functor (ReaderT r m)
```

These types often have a way to map a natural transformation, an arrow between two `Functor`s,
over that parameter.

```haskell
-- The type of natural transformations
type (~>) f g = forall x. f x -> g x

mapRight :: (g ~> g') -> Sum f g ~> Sum f g'
mapRight _  (InL fx) = InL fx
mapRight nt (InR gx) = InR (nt gx)

mapReaderT :: (m a -> n b) -> ReaderT r m a -> ReaderT r n b

-- mapReaderT can be used to map natural transformation
mapReaderT' :: (m ~> n) -> (ReaderT r m ~> ReaderT r n)
mapReaderT' naturalTrans = mapReaderT naturalTrans
```

The type class `FFunctor` abstracts such functions.

```haskell
class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
    ffmap :: (Functor g, Functor h) => (g ~> h) -> ff g x -> ff h x

ffmap :: (Functor g, Functor g') => (g ~> g') -> Sum f g x -> Sum f g' x
ffmap :: (Functor m, Functor n)  => (m ~> n) -> ReaderT r m x -> ReaderT r n x
```

Not all but many `FFunctor` instances can, in addition to `ffmap`, support `Monad`-like operations.

```haskell
class (FFunctor mm) => FMonad mm where
    fpure :: (Functor g) => g ~> mm g
    fjoin :: (Functor g) => mm (mm g) ~> mm g
```

Both of the above examples, `Sum` and `ReaderT r`, supports these operations.

```haskell
instance Functor f => FMonad (Sum f) where
    fpure :: (Functor g) => g ~> Sum f g
    fpure = InR

    fjoin :: (Functor g) => Sum f (Sum f g) ~> Sum f g
    fjoin (InL fx)       = InL fx
    fjoin (InR (InL fx)) = InL fx
    fjoin (InR (InR gx)) = InR gx

instance FMonad (ReaderT r) where
    fpure :: (Functor m) => m ~> ReaderT r m
    -- return :: x -> (e -> x)
    fpure = ReaderT . return

    fjoin :: (Functor m) => ReaderT r (ReaderT r m) ~> ReaderT r m
    -- join :: (e -> e -> x) -> (e -> x)
    fjoin = ReaderT . join . fmap runReaderT . runReaderT
```

## Comparison against similar type classes

There are similar type classes in other packages.

**TODO** write comparison

* From "mmorph": `MFunctor`, `MMonad`
* From "index-core": `IFunctor`, `IMonad`
* From "functor-combinators": `HFunctor`, `HInject`, `HBind`