# free-applicative-t

[![At Hackage](https://img.shields.io/hackage/v/free-applicative-t.svg)](https://hackage.haskell.org/package/free-applicative-t)

This package provides `ApT`, the "free" "applicative transformer" filling the empty corner in the table below.

| Free |    | -transformer |
|----|----|----|
|Monad| [Free](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Monad-Free.html#t:Free) | [FreeT](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Monad-Trans-Free.html#t:FreeT) |
|Applicative| [Ap](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Applicative-Free.html#t:Ap) | ??? |

## Why not `Control.Applicative.Trans.Free`?

There already is a type designated to be the free applicative transformer: [ApT](https://hackage.haskell.org/package/free-5.1.10/docs/Control-Applicative-Trans-Free.html#t:ApT) in the package [free](https://hackage.haskell.org/package/free-5.1.10/). Why do we do it again?

The applicative defined in `Control.Applicative.Trans.Free` is different to what this package provides. The difference is clear in how it is interpreted to another applicative:

``` haskell
-- "free" Control.Applicative.Trans.Free
runApT :: (Applicative h, Functor g) => (forall a. f a -> h a) -> (forall a. g (h a) -> h a) -> ApT f g b -> h b

-- "free-applicative-t" Control.Applicative.Trans.FreeAp
foldApT :: forall f g h b. Applicative h => (forall a. f a -> h a) -> (forall a. g a -> h a) -> ApT f g b -> h b
```

Although I (the author) believe this package provides the free applicative transformer under the most natural interpretation of "free" and "applicative transformer," the term "applicative transformer" has never been defined clearly and thus "free" thing of the "applicative transformer" hasn't been too.
Because of this ambiguity, I want it to be another take on the Free Applicative Transformer, rather than the patch to the "free" package replacing the current `Control.Applicative.Trans.Free`.
