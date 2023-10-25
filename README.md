# functor-monad

This repository contains multiple (currently: 3) Haskell packages.

## free-applicative-t

The package **free-applicative-t** provides the single module `Control.Applicative.Trans.FreeAp` for single type: `ApT`.
This type is supposed to represent the "free" "applicative transformer",
filling the space in this table:

| Free |    | -transformer |
|----|----|----|
|Monad| [Free](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Monad-Free.html#t:Free) | [FreeT](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Monad-Trans-Free.html#t:FreeT) |
|Applicative| [Ap](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Applicative-Free.html#t:Ap) | ??? |

More on [the README of the package itself](free-applicative-t/README.md).

## day-comonoid

The package **day-comonoid** provides a type class named `Comonoid`.

```haskell
class Comonad f => Comonoid f where
    coapply :: f a -> Day f f a
```

The name "Comonoid" should be read in a context. A functor `f` being `Comonoid` means it's a comonoid in the category of `Functor`s
equipped with [Day](https://hackage.haskell.org/package/kan-extensions-5.2.5/docs/Data-Functor-Day.html) as its tensor product.

`Comonoid` can be seen as "the dual" of `Applicative`, because `Applicative` can be seen as the type class for monoids in that category.

## functor-monad

The package **functor-monad** provides `FFunctor` and `FMonad`,
each corresponds to `Functor` and `Monad` but is higher-order.

|      | a Functor `f`   | a FFunctor `ff` |
|----|----|----|
| Takes | `a :: Type` | `g :: Type -> Type`, `Functor g` |
| Makes | `f a :: Type` | `ff g :: Type -> Type`, `Functor (ff g)` |
| Methods | `fmap :: (a -> b) -> f a -> f b` | `ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g ~> ff h)` |

|      | a Monad `m`   | a FMonad `mm` |
|----|----|----|
| Superclass | Functor | FFunctor |
| Methods | `return = pure :: a -> m a` | `fpure :: (Functor g) => g ~> mm g` |
|        | `(=<<) :: (a -> m b) -> m a -> m b` | `fbind :: (Functor g, Functor h) => (g ~> mm h) -> (mm g ~> mm h)` |
|        | `join :: m (m a) -> m a` | `fjoin :: (Functor g) => mm (mm g) ~> mm g` |

More on [the README of the package itself](functor-monad/README.md).