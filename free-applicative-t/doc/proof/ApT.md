|Status|Confirmed ver|
|----|----|
|WIP| |

# Properties of `ApT`

## Preliminary definitions

`ApT` and its instances are defined as follows.

```haskell
data ApT f g x =
      PureT (g x)
    | forall a b c. ApT (a -> b -> c -> x) (g a) (f b) (ApT f g c)

instance Functor g => Functor (ApT f g) where
    fmap h (PureT gx) = PureT $ fmap h gx
    fmap h (ApT x ga fb rc) = ApT (\a b c -> h (x a b c)) ga fb rc

instance Applicative g => Applicative (ApT f g) where
    pure = PureT . pure
    PureT gx <*> PureT gy = PureT (gx <*> gy)
    PureT gx <*> ApT y ga fb rc = ApT (\ ~(x,a) b c -> x (y a b c)) (liftA2 (,) gx ga) fb rc
    ApT x ga fb rc <*> rest = ApT (\a b ~(c,y) -> x a b c y) ga fb (liftA2 (,) rc rest)
```

<!--
For the purpose of proof, define the length of an `ApT` as follows:

```haskell
len :: ApT f g x -> Natural
len (PureT _) = 0
len (ApT _ _ r) = 1 + len r
```
-->

### Equivalence (≡) rather than strict equals (=)

The `ApT` constructor uses existentially quantified type. For this reason,
two values `u, v :: ApT f g x` with different field can be indistinguishable.

For example, consider the following `u` and `v`:

```haskell
instance Applicative F
fx :: F ()
gy :: G Int

u, v :: ApT F G Int
u = ApT (\a _ c -> a + c) gy fx (PureT gy)
v = ApT (\a _ c -> negate a + c) (negate <$> gy) fx (PureT gy)  
```

The field of `u` and `v` are not equal. But due to the existential quantification,
no program of type `ApT F G Int -> Bool` can expose the differece of `u` and `v`.

For any type `t` let `≡` be the relation on `t` such that for any `x,y :: t`, `x ≡ y` is equivalent to `∀(f :: t -> Bool). f x = f y`.

In other words, `≡` is the relation of two values which can't be differentiated by a function.
It is an equivalence relation.

The `Applicative` law of `ApT` hold only up to this equivalence relation `≡`.

These are the facts about equivalence relation `≡` on `ApT`:

* When `gx ≡ gx'`, then `PureT gx ≡ PureT gx'`
* When `x ≡ x'`, `ga ≡ ga'`, `fb ≡ fb'`, `rc ≡ rc'`, then `ApT x ga fb rc ≡ ApT x' ga' fb' rc'`
* Moving `fmap` around existential quantification
  * `ApT (\a b c -> x (k a) b c) ga fb rc ≡ ApT x (fmap k ga) fb rc`
  * `ApT (\a b c -> x a (k b) c) ga fb rc ≡ ApT x ga (fmap k fb) rc`
  * `ApT (\a b c -> x a b (k c)) ga fb rc ≡ ApT x ga fb (fmap k rc)`

In the above example of `u v :: ApT F G Int`, it can't be said that `u = v`, but `u ≡ v` holds.

### Auxiliary lemma

Suppose `g` is `Applicative` obeying all the laws. Define `prod` as follows.

```haskell
prod :: Applicative g => g a -> g b -> g (a,b)
prod = liftA2 (,)
```

From the Applicative laws of `g`, the following property holds:

```haskell
liftA2 op x y = uncurry op <$> x `prod` y
(x `prod` y) `prod` z ≡ assoc <$> x `prod` (y `prod` z)

assoc :: (x,(y,z)) -> ((x,y),z)
assoc (x,(y,z)) = ((x,y),z)
```

## `ApT f g` is a lawful `Applicative

### Proof plan

This document proves, instead of proving the Applicative laws defined on the documentation of [Applicative](https://hackage.haskell.org/package/base-4.17.0.0/docs/Control-Applicative.html#g:1),
the following set of properties.

* Left identity

  ```haskell
  pure f <*> y ≡ f <$> y
  ```

* Right identity

  ```haskell
  x <*> pure b ≡ flip ($ b) <$> x
  ```

* Composition
  
  ```haskell
  (.) <$> u <*> v <*> w ≡ u <*> (v <*> w)
  ```

The above set is equivalent to the original laws, assuming the following properties which holds by parametricity.

* Naturality
  
  These three equations hold:
  
  ```haskell
  fmap f (pure a) ≡ pure (f a)

  g <$> (x <*> y) ≡ (g .) <$> x <*> y

  x <*> (h <$> y) ≡ (. h) <$> x <*> y
  ```

### Proof

* Left identity

  * Case `y = PureT gy`

    ```haskell
    pure f <*> y
      ≡ PureT (pure f) <*> PureT gy
      ≡ PureT (pure f <*> gy)
      -- By the Applicative law of g
      ≡ PureT (fmap f gy)
      -- By definition of fmap 
      ≡ fmap f (PureT gy)
      ≡ fmap f y
    ```

  * Case `y = ApT y ga fb rc`

    ```haskell
    pure f <*> y
      ≡ PureT (pure f) <*> ApT y ga fb rc
      ≡ ApT (\ ~(x,a) b c -> x (y a b c)) (liftA2 (,) (pure f) ga) fb rc
      -- By the Applicative law of g
      ≡ ApT (\ ~(x,a) b c -> x (y a b c)) (fmap ((, ) f) ga) fb rc
      -- By moving fmap 
      ≡ ApT (\ a b c -> (\ ~(x,a) b c -> x (y a b c)) (f,a) b c) ga fb rc
      ≡ ApT (\ a b c -> f (y a b c)) ga fb rc
      -- By definition of fmap 
      ≡ f <$> ApT y ga fb rc
    ```

* Right identity

  Induction on `x`.

  * Case `x = PureT gx`

    ```haskell
    x <*> pure b
      ≡ PureT gx <*> PureT (pure b)
      -- Definition of <*>
      ≡ PureT (gx <*> pure b)
      -- Applicative law of g
      ≡ PureT (fmap ($b) gx)
      -- Definition of fmap 
      ≡ fmap ($b) (PureT gx)
      ≡ fmap ($b) x
    ```

  * Case `x = ApT x ga fb rc`

    ```haskell
    x <*> pure y
      ≡ ApT x ga fb rc <*> pure y
      -- Definition of <*>
      ≡ ApT (\a b ~(c,y) -> x a b c y) ga fb (liftA2 (,) rc (pure y))
      -- Definition of liftA2
      ≡ ApT (\a b ~(c,y) -> x a b c y) ga fb (fmap (,) rc <*> pure y)
      -- Applicative law of g
      ≡ ApT (\a b ~(c,y) -> x a b c y) ga fb (fmap ($ y) (fmap (,) rc))
      -- Functor law of g
      ≡ ApT (\a b ~(c,y) -> x a b c y) ga fb ((, y) <$> rc)
      -- By moving fmap
      ≡ ApT (\ a b c -> (\a b ~(c,y) -> x a b c y) a b (c,y)) ga fb rc
      ≡ ApT (\ a b c -> (x a b c) y) ga fb rc
      -- By definition of fmap 
      ≡ fmap ($ y) (ApT x ga fb rc)
      ≡ fmap ($ y) x
    ```

* Composition
  
  Induction on `u`.

  * Case `u = ApT x fa gb rc`

    ```haskell
    u <*> (v <*> w)
     ≡ ApT x fa gb rc <*> (v <*> w)
     ≡ ApT x' fa gb (rc `prod` (v <*> w))
          where x' a b ~(c,vw) = x a b c vw
     -- Definition of prod
     ≡ ApT x' fa gb ((,) <$> rc <*> (v <*> w))
     -- By induction hypothesis
     ≡ ApT x' fa gb ((.) <$> ((,) <$> rc) <*> v <*> w)
     ≡ ApT x' fa gb ((\c v w -> (c, v w)) <$> rc <*> v <*> w)
     ≡ ApT (\x' a b ~(c,vw) -> x a b c vw) fa gb ((\c v w -> (c, v w)) <$> rc <*> v <*> w)

    (.) <$> u <*> v <*> w
     ≡ (.) <$> ApT x fa gb rc <*> v <*> w
     ≡ ApT (\a b c -> (.) (x a b c)) fa gb rc <*> v <*> w
     ≡ ApT x' fa gb (rc `prod` v) <*> w
          where x' a b ~(c,v) = (.) (x a b c) v
     ≡ ApT x'' fa gb ((rc `prod` v) `prod` w)
          where x' a b ~(c,v) = (.) (x a b c) v
                x'' a b ~(~(c,v), w) = x' a b ~(c,v) w
                                 = (.) (x a b c) v w
                                 = (x a b c . v) w
                                 = x a b c (v w)
     ≡ ApT x'' fa gb ((rc `prod` v) `prod` w)
          where x'' a b ~(~(c,v), w) = x a b c (v w)
     ≡ ApT (\a b cvw -> x''' a b (p cvw)) fa gb ((rc `prod` v) `prod` w)
          where x''' a b ~(c,vw) = x a b c vw
                p ~(~(c,v),w) = (c, v w)
     ≡ ApT x''' fa gb (p <$> (rc `prod` v) `prod` w)
     ≡ ApT x''' fa gb ((\c v w -> (c, vw)) <$> rc <*> v <*> w)
     ≡ ApT (\x' a b ~(c,vw) -> x a b c vw) fa gb ((\c v w -> (c, vw)) <$> rc <*> v <*> w)
     ≡ u <*> (v <*> w)
    ```

  * Case `u = PureT gu`
    
    Case analysis on `v` and `w`.

    * `v = PureT gv, w = PureT gw`

      ```haskell
      (.) <$> u <*> v <*> w
       ≡ (.) <$> PureT gu <*> PureT gv <*> PureT gw
       -- Definition of fmap and <*>
       ≡ PureT ((.) <$> gu <*> gv <*> gw)
       -- Applicative law of g
       ≡ PureT (gu <*> (gv <*> gw))
       -- Definition of <*>
       ≡ PureT gu <*> (PureT gv <*> PureT gw)
       ≡ u <*> (v <*> w)
      ```

    * `v = PureT gv, w = ApT z ga fb rc`

      ```haskell
      u <*> (v <*> w)
       ≡ PureT gu (PureT gv <*> ApT z ga fb rc)
       ≡ PureT gu <*> ApT ((\ ~(v,a) b c -> v (z a b c))) (gv `prod` ga) fb rc
       ≡ ApT (\~(u,~(v,a)) b c -> u (v (z a b c)) vw b c)
              (gu `prod` (gv `prod` ga))
              fb rc
       ≡ ApT (\~(u,~(v,a)) b c -> u (v (z a b c)))
              (assoc <$> (gu `prod` gv) `prod` ga)
              fb rc
       ≡ ApT (\~((u,v),a) b c -> u (v (z a b c)))
              ((gu `prod` gv) `prod` ga)
              fb rc
      (.) <$> u <*> v <*> w
       ≡ (.) <$> PureT gu <*> PureT gv <*> ApT z ga fb rc
       -- Definition of fmap and <*>
       ≡ ApT (\ ~(x,a) b c -> x (z a b c)) ((liftA2 (.) gu gv) `prod` ga) fb rc
       -- Applicative law of g
       ≡ ApT (\ ~(x,a) b c -> x (z a b c))
              (first (uncurry (.)) <$> (gu `prod` gv) `prod` ga)
              fb rc
       -- Move fmap
       ≡ ApT (\uva b c -> (\ ~(x,a) b c -> x (z a b c)) (first (uncurry (.)) uva) b c
              ((gu `prod` gv) `prod` ga)
              fb rc
       ≡ ApT (\~((u,v),a) b c -> (u . v) (z a b c))
              ((gu `prod` gv) `prod` ga)
              fb rc
       ≡ ApT (\~(u,(v,a)) b c -> u (v (z a b c)))
              ((gu `prod` gv) `prod` ga)
              fb rc
       ≡ u <*> (v <*> w)
      ```

    * Case `v = ApT y ga fb rc`

        ```haskell
        u <*> (v <*> w)
        ≡ PureT gu <*> (ApT y ga fb rc <*> w)
        -- Definition of <*>
        ≡ PureT gu <*> ApT (\a b ~(c,z) -> y a b c z) ga fb (rc `prod` w)
        -- Definition of <*>
        ≡ ApT (\~(x,a) b ~(c,z) -> x (y a b c z)) (gu `prod` ga) fb (rc `prod` w)
        
        (.) <$> u <*> v <*> w
        ≡ (.) <$> PureT gu <*> ApT y ga fb rc <*> w
        -- Definition of fmap and <*>
        ≡ ApT (\~(x,a) b c -> x (y a b c)) (fmap (first (.)) (gu `prod` ga) fb rc <*> w
        -- Move fmap
        ≡ ApT (\~(x,a) b c -> x . y a b c) (gu `prod` ga) fb rc <*> w
        -- Definition of <*>
        ≡ ApT (\~(x,a) b ~(c,z) -> (x . y a b c) z) (gu `prod` ga) fb (rc `prod` w)
        ≡ ApT (\~(x,a) b ~(c,z) -> x (y a b c z)) (gu `prod` ga) fb (rc `prod` w)
        ≡ u <*> (v <*> w)
        ```

## `liftT` is an applicative transformation
## Universal properties of `ApT`