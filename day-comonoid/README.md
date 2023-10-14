# day-comonid: The(?) dual of Applicative

This package provides a type class named `Comonoid`.

```haskell
class Comonad f => Comonoid f where
    coapply :: f a -> Day f f a
```

The name "Comonoid" should be read in a context. A functor `f` being `Comonoid` means it's a comonoid in the category of `Functor`s
equipped with [Day](https://hackage.haskell.org/package/kan-extensions-5.2.5/docs/Data-Functor-Day.html) as its tensor product.

`Comonoid` can be contrasted with `Applicative`, which is equivalent to a type class for monoids in the said category of `Functor`s.

```haskell
class Functor f => Applicative f where
    pure  :: a -> f a
    (<*>) :: f (a -> b) -> f a -> f b

-- A hypothetical type class equivalent to Applicative
class Functor f => DayMonoid f where
    pure' :: Identity a -> f a
    default pure' :: Applicative f => Identity a -> f a
    pure' = pure . runIdentity

    ap' :: Day f f a -> f a
    default ap' :: Applicative f => Day f f a -> f a
    ap' = dap
```

`Comonoid` is related to [Comonad](https://hackage.haskell.org/package/comonad-5.0.8/docs/Control-Comonad.html),
just like `Applicative` is related to `Monad`.

`Applicative` is a superclass of `Monad` *just because*
any `Monad f` instance is sufficient to implement `Applicative f` in a certain way.

Similarly, `Comonad` is a superclass of `Comonoid`,
*just because* having `(extract :: f a -> a)` and `coapply` is sufficient to make `f` a `Comonad`.

| `Applicative` | `=>` | `Monad` |
|----|----|----|
| `a -> f a`    |      | `a -> f a` |
| `Day f f a -> f a` |  | `f (f a) -> f a` |

| `Comonoid` | `<=` | `Comonad` |
|----|----|----|
| `f a -> a`    |      | `f a -> a` |
| `f a -> Day f f a` |  | `f a -> f (f a)` |

Both of these relations are rooted in the same fact that the following conversion is possible for any `Functor f` and `Functor g`:

```haskell
dayToCompose :: (Functor f, Functor g) => Day f g a -> f (g a)
dayToCompose (Day fb fc op) = fmap (\b -> fmap (op b) fc) fb
```
