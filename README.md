# functor-monad

This repository contains multiple (currently: 2) Haskell packages.

## free-applicative-t

The package **free-applicative-t** provides the single module `Control.Applicative.Trans.FreeAp` for single type: `ApT`.
This type is supposed to represent the "free" "applicative transformer",
filling the space in this table:

| Free |    | -transformer |
|----|----|----|
|Monad| [Free](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Monad-Free.html#t:Free) | [FreeT](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Monad-Trans-Free.html#t:FreeT) |
|Applicative| [Ap](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Applicative-Free.html#t:Ap) | ??? |

More on [the README of the package itself](free-applicative-t/README.md).

## functor-monad

The package **functor-monad** provides `FFunctor` and `FMonad`,
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

More on [the README of the package itself](functor-monad/README.md).