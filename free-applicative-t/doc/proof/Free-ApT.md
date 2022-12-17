|Status|Confirmed ver|
|----|----|
|WIP| free-5.1.10 |

# Properties of `Control.Applicative.Trans.Free.ApT` in free

This documents properties of `Control.Applicative.Trans.Free.ApT`.

## Definitions

The implementation of `ApT` in package [free](https://hackage.haskell.org/package/free-5.1.10/) is:

https://github.com/ekmett/free/blob/df5cea9a9e4bbce83ebfe1e090aeb97801da63c2/src/Control/Applicative/Trans/Free.hs#L65-L68

https://github.com/ekmett/free/blob/df5cea9a9e4bbce83ebfe1e090aeb97801da63c2/src/Control/Applicative/Trans/Free.hs#L75

https://github.com/ekmett/free/blob/df5cea9a9e4bbce83ebfe1e090aeb97801da63c2/src/Control/Applicative/Trans/Free.hs#L87-L99

## Alternative definition of `Applicative (ApT f g)` instance

Instances `ApT` and `ApF` are defined mutually recursively.
But by expanding `<*>` for `ApT` in the `ApF` instance, we can get self recursive `ApF` instance and
non-recursive `ApT` instance.

```haskell
instance Applicative g => Applicative (ApF f g) where
  pure = Pure

  Pure f        <*> y       = fmap f y      -- fmap
  y             <*> Pure a  = fmap ($ a) y  -- interchange

  -- [**]
  Ap a (ApT gf) <*> b       = a `Ap` (flip <$> ApT gf <*> ApT (pure b))

instance Applicative g => Applicative (ApT f g) where
  pure = ApT . pure . pure
  ApT xs <*> ApT ys = ApT ((<*>) <$> xs <*> ys)
```

The line below `[**]` can be rewritten by expanding the definition of `ApT` instances and using `Applicative` laws of `g`.

```haskell
-- [**]
Ap a (ApT gf) <*> b  = a `Ap` (flip <$> ApT gf <*> ApT (pure b))
    -- By definition of fmap on (ApT f g)
  = a `Ap` (ApT $ ApT (fmap flip <$> gf) <*> ApT (pure b))
    -- By definition of (<*>) on (ApT f g)
  = a `Ap` (ApT $ (<*>) <$> (fmap flip <$> gf) <*> pure b)
    -- By the Functor law of g
  = a `Ap` (ApT $ ((<*>) . fmap flip <$> gf) <*> pure b)
    -- By the interchange law (and the Functor law) of g
  = a `Ap` (ApT $ ($ b) . (<*>) . fmap flip <$> gf)
    -- use <&> instead of <$>
  = a `Ap` (ApT $ gf <&> ($ b) . (<*>) . fmap flip)
    --                   ^^^^^^^^^^^^^^^^^^^^^^^^^   [***]
  = a `Ap` (ApT $ gf <&> (\f -> fmap flip f <*> b))

-- (***)
($ b) . (<*>) . fmap flip
  = \f -> ($ b) ((<*>) (fmap flip f))
  = \f -> fmap flip f <*> b
```

The definition after rewriting do not need `Applicative g` instance, just `Functor g`.

```haskell
instance Functor g => Applicative (ApF f g) where
  pure = Pure

  Pure f        <*> y       = fmap f y      -- fmap
  y             <*> Pure a  = fmap ($ a) y  -- interchange
  Ap a (ApT gf) <*> b       = a `Ap` (ApT $ gf <&> (\f -> fmap flip f <*> b))
```

## Applicative laws on `ApF` instance

### Proof plan

Since `Applicative (ApT f g)` is equivalent to `Compose g (ApF f g)` instance up to `newtype` wrapping, we only need to prove the instance of `ApF f g` is lawful.

This document proves, instead of proving the Applicative laws defined on the documentation of [Applicative](https://hackage.haskell.org/package/base-4.17.0.0/docs/Control-Applicative.html#g:1),
the following set of properties.

* Left identity

  ```haskell
  f <$> pure a <*> y = f a <$> y
  ```

* Right identity

  ```haskell
  f <$> x <*> pure b = flip f b <$> u
  ```

* Composition
  
  ```haskell
  (.) <$> u <*> v <*> w = u <*> (v <*> w)
  ```

The above set is equivalent to the original laws, assuming the following properties which holds by parametricity.

* Naturality
  
  These three equations hold:
  
  ```haskell
  fmap f (pure a) = pure (f a)

  g <$> (x <*> y) = (g .) <$> x <*> y

  x <*> (h <$> y) = (. h) <$> x <*> y
  ```

### Proof

* Left identity

  ```haskell
  f <$> pure a <*> y
      -- By definition of pure and fmap
    = Pure (f a) <*> y
      -- By definition of fmap and <*>
    = f a <$> y
  ```

* Right identity

  Case analysis on x.

  When `x = Pure a`:

  ```haskell
  f <$> x <*> pure b
    = f <$> Pure a <*> pure b
    -- By left identity and definition of pure
    = f a <$> Pure b
    = Pure (f a b)
    = flip f b <$> Pure a 
  ```

  When `x = Ap _ _`:

  ```haskell
  f <$> x@(Ap _ _) <*> pure b
    -- By definition of pure
    = f <$> x <*> Pure b
    -- By definition of <*>
    = ($ b) <$> (f <$> x)
    -- By Functor law
    = (($ b) . f) <$> x
    = (\a -> f a b) <$> x
    = flip f b <$> x
  ```

* Composition
  
  Induction on `u`.

  Base case `u = Pure f`:

  ```haskell
  (.) <$> u <*> v <*> w
    = (.) <$> Pure f <*> v <*> w
    = Pure (f .) <*> v <*> w
    = fmap (f .) v <*> w
    -- Naturality
    = f <$> (v <*> w)
    = Pure f <*> (v <*> w)
    = u <*> (v <*> w)
  ```

  Induction case `u = Ap a (ApT gu')`

  ```haskell
  u <*> (v <*> w)
    = Ap a (ApT gu') <*> (v <*> w)
    = a `Ap` ApT (gu' <&> (\u' -> fmap flip u' <*> (v <*> w)))
      -- By induction hypothesis
    = a `Ap` ApT (gu' <&> (\u' -> (.) <$> fmap flip u' <*> v <*> w))
    = a `Ap` ApT (gu' <&> (\u' -> fmap ((.) . flip) u' <*> v <*> w))

  (.) <$> u <*> v <*> w
    = (.) <$> Ap a (ApT gu') <*> v <*> w
      -- By definition of fmap on ApF and ApT
    = Ap a (ApT (fmap ((.) .) <$> gu')) <*> v <*> w
    --                 ^^^^^ let bb = ((.) .)
    -- Use infix notation `Ap`
    -- use <&> instead of <$>
    = a `Ap` ApT (gu' <&> fmap bb) <*> v <*> w 
    -- By definition of <*>
    = a `Ap` ApT (gu' <&> fmap bb <&> (\u' -> fmap flip u' <*> v)) <*> w
    -- By definition of <*>
    = a `Ap` ApT (gu' <&> fmap bb <&> (\u' -> fmap flip u' <*> v) <&> (\uv' -> fmap flip uv' <*> w))
    -- By Functor law (in terms of <&>)
    = a `Ap` ApT (gu' <&> (\u' -> fmap flip (fmap flip (fmap bb u') <*> v) <*> w))
    --                            ^^^^^^^^^--------------------------------^^^
    -- By Naturality
    --                             vvvvvvvvvvvvv---------------------------------vvv
    = a `Ap` ApT (gu' <&> (\u' -> (fmap (flip .) (fmap flip (fmap bb u')) <*> v) <*> w))
    -- By Functor law
    = a `Ap` ApT (gu' <&> (\u' -> fmap ((flip .) . flip . bb) u' <*> v <*> w))
    --                                  ^^^^^^^^^^^^^^^^^^^^ -- [***]
    = a `Ap` ApT (gu' <&> (\u' -> fmap ((.) . flip) u' <*> v <*> w))
  
  -- [***]
  bb f x g y
    = ((.) .) f x g y
    = ((.) .) f x g y
    = ((.) . f) x g y
    = (.) (f x) g y
    = (f x . g) y
    = f x (g y)
  (flip .) . flip
    = \f -> flip . flip f
    = \f x y z -> flip (flip f x) y z
    = \f x y z -> (flip f x) z y
    = \f x y z -> f z x y
  (flip .) . flip . bb
    = \f -> ((flip .) . flip) (bb f)
    = \f g y z -> bb f z g y
    = \f g y z -> f z (g y)
    = \f g y z -> flip f (g y) z
    = \f g y -> flip f (g y)
    = \f g -> flip f . g
    = \f -> (.) (flip f)
    = (.) . flip

  ```
  