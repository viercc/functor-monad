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

Constructor `ApT` uses existentially quantified type. For this reason,
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

The field of `u` and `v` are not equal. But no program of type `ApT F G Int -> Bool` can expose the differece of `u` and `v`, by how the existential quantification works in GHC.

The `Applicative` law of `ApT` we're trying to prove also doesn't hold in the equality (`=`) sense, but only up to an equivalence relation `≡`, which expresses "is indistinguishable each other" relation.

Let `≡` be the relation defined on every type `t` such that for any `x,y :: t`, `x ≡ y` is equivalent to `∀(f :: t -> Bool). f x = f y`.
In other words, `≡` is the relation of two values which can't be distinguished by a function.
It is an equivalence relation.

In the above example of `u v :: ApT F G Int`, it can't be said that `u = v`, but `u ≡ v` holds.

### Alternative definition in terms of `Day` combinator

Although the definition of `ApT` in the actual implementation is good to write in the code, it is not convenient to prove the properties we're going for.

Instead of the actual definition, the following `ApT'` can be used.

```haskell
import Data.Functor.Day
import Data.Functor.Sum

type (⊗) = Day
infixr 4 ⊗ -- Right associative

type (+) = Sum
newtype ApT' f g x = Roll { unroll :: (g + g ⊗ f ⊗ ApT' f g) x }
```

Here, `Day` and `Sum`, written using operators `⊗` and `+` respectively, is defined as follows:

```haskell
data Day f g x = forall a b. Day (f a) (g b) (a -> b -> x)
data Sum f g x = InL (f x) | InR (g x)
```

`ApT'` is isomorphic to `ApT` (up to `≡`) by the following pair of natural transformations.

```haskell
-- Type of natural transformation
type f ~> g = forall x. f x -> g x
infix 1 ~>

to :: ApT f g ~> ApT' f g
to = Roll . toRep

from :: ApT' f g ~> ApT f g
from = fromRep . unroll

toRep :: ApT f g ~> (g + g ⊗ f ⊗ ApT' f g)
toRep (PureT gx) = InL $ intro2 gx
toRep (ApT x ga fb rc) = InR $ Day ga (Day fb (to rc) (,)) (\a (b,c) -> x a b c)

fromRep :: (g + g ⊗ f ⊗ ApT' f g) ~> ApT f g
fromRep (InL gx) = PureT gx
fromRep (InR (Day ga (InR (Day fb rc op2)) op1)) = ApT (\a b c -> op1 a (op2 b c)) ga fb (from rc)
```

The fact they are actually isomorphisms, which is stated in equations below, must be proven later.

* `from . to = fromRep . toRep ≡ id`
* `to . from ≡ id`
  * Or equivalently: `toRep . fromRep ≡ id`

The `Applicative` operations can be translated to `ApT'` too.

```haskell
instance Applicative g => Applicative (ApT' f g) where
  pure = Roll . InL . pure
  f <*> g = day f g               -- ApT' f g ⊗ ApT' f g
          & trans1 unroll         --   -> (g + g ⊗ f ⊗ ApT' f g) ⊗ ApT' f g
          & distributeRight       --   -> g ⊗ ApT' f g + (g ⊗ f ⊗ ApT' f g) ⊗ ApT' f g
          & eitherSum actG apRecurse

-- > eitherSum p q . InL = p
-- > eitherSum p q . InR = q
-- > eitherSum InL InR = id
-- > t . eitherSum p q = eitherSum (t . p) (t . q)
eitherSum :: (f ~> h) -> (g ~> h) -> (f + g ~> h)
eitherSum fh gh (InL fx) = fh fx
eitherSum fh gh (InR gx) = gh gx

-- > transSum p q = eitherSum (InL . p) (InR . q)
transSum :: (f ~> f') -> (g ~> g') -> (f + g ~> f' + g')
transSum p q fg = case fg of { InL fx -> InL (p fx); InR gx -> InR (q gx) }

distributeRight :: (f + g) ⊗ h ~> f ⊗ h + g ⊗ h
distributeRight (Day (InL fa) hb op) = InL (Day fa hb op)
distributeRight (Day (InR ga) hb op) = InR (Day ga hb op)

distributeLeft :: f ⊗ (g + h) ~> f ⊗ g + f ⊗ h
distributeLeft (Day fa (InL gb) op) = InL (Day fa gb op)
distributeLeft (Day fa (InR hb) op) = InR (Day fa hb op)

actG :: Applicative g => (g ⊗ ApT' f g) ~> ApT' f g
actG =                    --    g ⊗ ApT' f g
      trans2 unroll       -- -> g ⊗ (g + g ⊗ f ⊗ ApT' f g)
  >>> distributeLeft      -- -> g ⊗ g + g ⊗ g ⊗ f ⊗ ApT' f g
  >>> transSum dap (trans1 dap . assoc)
                        -- -> g + g ⊗ f ⊗ ApT' f g
  >>> Roll

apRecurse :: Applicative g => (g ⊗ f ⊗ ApT' f g) ⊗ ApT' f g ~> ApT' f g
apRecurse gfApAp =
                         --    (g ⊗ f ⊗ ApT' f g) ⊗ ApT' f g
  >>> disassoc             -- -> g ⊗ (f ⊗ ApT' f g) ⊗ ApT' f g
  >>> trans2 disassoc      -- -> g ⊗ f ⊗ (ApT' f g ⊗ ApT' f g)
  >>> trans2 (trans2 dap)  -- -> g ⊗ f ⊗ ApT' f g
  >>> InR >>> Roll         -- -> ApT' f g
```

The isomorphism `from, to` are an applicative transformations. Again, it must be proven later.

## Isomorphism between `ApT`

`to` and `from` are inverses each other. Equivalently, `to` and `from` are too.

### `from . to ≡ id`

To show `from . to ≡ id` is to show for all `u :: ApT f g x`, `from (to u) ≡ u`.
Because `from . to = fromRep . unroll . Roll . toRep = fromRep . toRep`, 
one only needs to show `fromRep (toRep u) ≡ u`.

Induction on `u`.

* `u = PureT gx`

  ```haskell
  fromRep (toRep u)
   = fromRep (toRep (PureT gx))
   = fromRep (InL gx)
   = PureT gx
   = u
  ```

* `u = ApT x ga fb rc`

  ```haskell
  fromRep (toRep (ApT x ga fb rc))
   = fromRep $ InR $ Day ga (Day fb (to rc) (,)) (\a (b,c) -> x a b c)
   = let op1 = \a (b,c) -> x a b c
         op2 = (,)
      in ApT (\a b c -> op1 a (op2 b c)) ga fb (from (to rc))
   = ApT (\a b c -> x a b c) ga fb (from (to rc))
     -- Induction hypothesis
   ≡ ApT x ga fb rc
   = u
  ```

### `to . from ≡ id`

To show `to . from ≡ id` is to show for all
`u' :: ApT' f g x`, `from (to u) ≡ u`.

Induction on `u`.

* `u = Roll (InL gx) `

  ```haskell
  to (from u)
   = Roll . toRep . fromRep . unroll $ Roll (InL gx)
   = Roll . toRep (PureT gx)
   = Roll $ InL gx
   = u
  ```

* `u = Roll . InR $ Day ga (Day fb rc op2) op1`

  ```haskell
  to (from u)
   = Roll . toRep . fromRep . unroll . Roll . InR $ Day ga (Day fb rc op2) op1
   = Roll . toRep $ ApT (\a b c -> op1 a (op2 b c)) ga fb (from rc)
   = let op1' = \a (b,c) -> op1 a (op2 b c)
      in Roll . InR $ Day ga (Day fb (to (from rc)) (,)) op1'
   = let op1' = \a bc -> op1 a (uncurry op2 bc)
      in Roll . InR $ Day ga (Day fb (to (from rc)) (,)) op1'
   -- Dinaturality
   ≡ Roll . InR $ Day ga (fmap (uncurry op2) (Day fb (to (from rc)) (,))) op1
   = Roll . InR $ Day ga (Day fb (to (from rc)) op2) op1
   -- Induction hypothesis
   ≡ Roll . InR $ Day ga (Day fb rc op2) op1
   = u
  ```

### `to` is an applicative homomorphism

`to` preserves `pure`. In other words, `to (pure a) ≡ pure a` holds for any `a`.

```haskell
to (pure a)
 = to (PureT (pure a))
 = Roll . InL (pure a)
 = pure a
```

`to` preserves `<*>`. In other words, `to (u <*> v) ≡ to u <*> to v ` holds for any `u,v`.

Induction on `u`.

* `u = PureT gx` case.
  
  Case on `v`.

  * `v = PureT gy` case.

    ```haskell
    to (u <*> v)
     = to (PureT gx <*> PureT gy)
     = to (PureT (gx <*> gy))
     = Roll . InL $ gx <*> gy
    to u <*> to v
     = to (PureT gx) <*> to (PureT gy)
     = (Roll $ InL gx) <*> (Roll $ InL gy)
     = actG (day gx (Roll $ InL gy))
     = day gx (InL gy) & distributeLeft & transSum dap _ & Roll
     = InL (day gx gy) & transSum dap _ & Roll
     = InL (dap (day gx gy)) & Roll
     = Roll $ InL (gx <*> gy)
     = to (u <*> v)
    ```
  
  * `v = ApT y ga fb rc` case.
    
    ```haskell
    to (u <*> v)
     = to (PureT gx <*> ApT y ga fb rc)
     = to $ ApT (\~(x,a) b c -> x (y a b c)) (liftA2 (,) gx ga) fb rc
     = Roll . InR $ Day (liftA2 (,) gx ga) (Day fb (to rc) (,)) (\(x,a) (b,c) -> x (y a b c))
    to u <*> to v
     = to (PureT gx) <*> to (ApT y ga fb rc)
     = let op a (b,c) = y a b c
           v' = Day ga (Day fb (to rc) (,)) op
        in Roll (InL gx) <*> (Roll (InR v'))
     = let op a (b,c) = y a b c
           v' = Day ga (Day fb (to rc) (,)) op
        in actG (day gx (Roll (InR v')))
     = let op a (b,c) = y a b c
           v' = Day ga (Day fb (to rc) (,)) op
        in day gx (InR v') & distributeLeft & transSum _ (trans1 dap . assoc) & Roll
      --   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
     = let op a (b,c) = y a b c
           v' = Day ga (Day fb (to rc) (,)) op
        in InR (day gx v') & transSum _ (trans1 dap . assoc) & Roll
       --  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
     = let op a (b,c) = y a b c
           v' = Day ga (Day fb (to rc) (,)) op
        in Roll $ InR (day gx v' & assoc & trans1 dap)
       --              ^^^^^^^^^
     = let op a (b,c) = y a b c
           uv' = Day gx (Day ga (Day fb (to rc) (,)) op) id
        in Roll $ InR (uv' & assoc & trans1 dap)
       --              ^^^^^^^^^^^
     = let op a (b,c) = y a b c
           op' (x,a) bc = id x (op a bc) 
           uv'' = Day (Day gx ga (,)) (Day fb (to rc) (,)) op'
        in Roll $ InR (uv'' & trans1 dap)
     = let op'' (x,a) (b,c) = x (y a b c) 
           uv''' = Day (dap (Day gx ga (,))) (Day fb (to rc) (,)) op''
        in Roll $ InR uv'''
     = let op'' (x,a) (b,c) = x (y a b c) 
           uv''' = Day (liftA2 (,) gx ga) (Day fb (to rc) (,)) op''
        in Roll $ InR uv'''
     = Roll . InR $ Day (liftA2 (,) gx ga) (Day fb (to rc) (,)) (\(x,a) (b,c) -> x (y a b c))
     = to (u <*> v)
    ```

* `u = ApT x ga fb rc` case.

  ```haskell
  to (u <*> v)
   = to (ApT x ga fb rc <*> v)
   = to (ApT (\a b (c,y) -> x a b c y) ga fb (liftA2 (,) rc v))
   = let xy = \a b (c,y) -> x a b c y
         op = \a (b, cy) -> xy a b cy
      in Roll . InR $ Day ga (Day fb (to (liftA2 (,) rc v)) (,)) op
   = let op = \a (b, (c,y)) -> x a b c y
      in Roll . InR $ Day ga (Day fb (to (liftA2 (,) rc v)) (,)) op
  to u <*> to v
   = to (ApT x ga fb rc) <*> to v
   = (Roll . InR $ Day ga (Day fb (to rc) (,)) (\a (b,c) -> x a b c)) <*> to v
   = apRecurse $ day (Day ga (Day fb (to rc) (,)) (\a (b,c) -> x a b c)) (to v)
   = let op = \a (b,c) -> x a b c
         uv = Day (Day ga (Day fb (to rc) (,)) op) (to v) id
      in uv & disassoc & trans2 disassoc & trans2 (trans2 dap)
   = let op = (\a (b,c) -> x a b c)
         op' = \a (bc,y) -> id (op a bc) y
         uv' = Day ga (Day (Day fb (to rc) (,)) (to y) (,)) op'
      in uv' & trans2 disassoc & trans2 (trans2 dap)
   = let op' = \a ((b,c),y) -> x a b c y
         op2' = \b (c,y) -> ((b,c), y)
         uv'' = Day ga (Day fb (Day (to rc) (to y) (,)) op2') op'
      in uv'' & trans2 (trans2 dap)
   = let op' = \a ((b,c),y) -> x a b c y
         op2' = \b (c,y) -> ((b,c), y)
         uv'' = Day ga (fmap (uncurry op2') (Day fb (Day (to rc) (to y) (,)) (,))) op'
      in uv'' & trans2 (trans2 dap)
   -- Dinaturality
   ≡ let op' = \a ((b,c),y) -> x a b c y
          op2' = \b (c,y) -> ((b,c), y)
          op'' = \a bcy -> op' a (uncurry op2' bcy)
          uv'' = Day ga (Day fb (Day (to rc) (to y) (,)) (,)) op''
       in uv'' & trans2 (trans2 dap)
   = let op'' = \a (b,(c,y)) -> x a b c y
         uv'' = Day ga (Day fb (Day (to rc) (to y) (,)) (,)) op''
      in uv'' & trans2 (trans2 dap)
   = let op'' = \a (b,(c,y)) -> x a b c y
         uv''' = Day ga (Day fb (dap (Day (to rc) (to y) (,))) (,)) op''
                          --     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
      in uv'''
   = let op'' = \a (b,(c,y)) -> x a b c y
      in Day ga (Day fb (liftA2 (,) (to rc) (to v)) (,)) op''
   --                    ^^^^^^^^^^^^^^^^^^^^^^^^^
   -- Induction hypothesis
   ≡ let op'' = \a (b,(c,y)) -> x a b c y
      in Day ga (Day fb (to (liftA2 (,) rc v)) (,)) op''
   = to (u <*> v)
  ```

## `ApT f g` is a lawful `Applicative`

### Proof plan

This document proves, instead of proving the Applicative laws defined on the documentation of [Applicative](https://hackage.haskell.org/package/base-4.17.0.0/docs/Control-Applicative.html#g:1),
the following set of properties. For any `Applicative h`, applicative law implies the following three equations:

* Left identity

  ```haskell
  dap . trans1 unit ≡ (elim1 :: Day Identity h ~> h)
    where unit = pure . runIdentity :: Identity ~> h
  ```

* Right identity

  ```haskell
  dap . trans2 unit ≡ (elim2 :: Day h Identity ~> h) 
  ```

* Composition
  
  ```haskell
  dap . trans2 dap ≡ (dap . trans1 dap . assoc :: Day h (Day h h))
  ```

Conversely, the above set implies the original laws.

Also, instead of proving these equations for `ApT f g`, it's enough to prove on `ApT' f g`,
because of the isomorphism `to, from` which preserves `pure` and `<*>`.

### Proof

* Left identity

  ```haskell
  dap . trans1 unit
   ≡ eitherSum actG apRecurse . distributeRight . trans1 unroll . trans1 (Roll . InL . unit)
   ≡ eitherSum actG apRecurse . distributeRight . trans1 (InL . unit)
   ≡ eitherSum actG apRecurse . InL . trans1 unit
   ≡ actG . trans1 unit
   ≡ Roll . transSum dap (trans1 dap . assoc) . distributeLeft . trans2 unroll . trans1 unit
   ≡ Roll . transSum dap (trans1 dap . assoc) . distributeLeft . trans1 unit . trans2 unroll
   ≡ Roll . transSum dap (trans1 dap . assoc)
           . transSum (trans1 unit) (trans1 unit) . distributeLeft . trans2 unroll
   ≡ Roll . transSum (dap . trans1 unit) (trans1 dap . assoc . trans1 unit)
      --               ^^^^^^^^^^^^^^^^^   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
           . distributeLeft . trans2 unroll
   ≡ Roll . transSum elim1 (trans1 elim1 . assoc) . distributeLeft . trans2 unroll
   ≡ Roll . transSum elim1 elim1 . distributeLeft . trans2 unroll
      --     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   ≡ Roll . elim1 . trans2 unroll
   ≡ Roll . unroll . elim1
   ≡ elim1
  ```

* Right identity
  
  ```haskell
  dap . trans2 unit
   ≡ eitherSum actG apRecurse . distributeRight . trans1 unroll . trans2 unit
   ≡ eitherSum actG apRecurse . distributeRight . trans2 unit . trans1 unroll
   ≡ eitherSum actG apRecurse . transSum (trans2 unit) (trans2 unit) .
         . distributeRight . trans1 unroll
   ≡ eitherSum (actG . trans2 unit) (apRecurse . trans2 unit)
         . distributeRight . trans1 unroll
  actG . trans2 unit
   ≡ Roll . transSum dap (trans1 dap . assoc)
        . distributeLeft . trans2 unroll . trans2 unit
   ≡ Roll . transSum dap (trans1 dap . assoc)
           . distributeLeft . trans2 (InL . unit)
   ≡ Roll . transSum dap (trans1 dap . assoc)
           . InL . trans2 unit
   ≡ Roll . InL . dap . trans2 unit
   ≡ Roll . InL . dap . trans2 unit
   ≡ Roll . InL . elim2
  apRecurse . trans2 unit
   ≡ Roll . InR . trans2 (trans2 dap) . trans2 disassoc . disassoc . trans2 unit
   ≡ Roll . InR . trans2 (trans2 dap) . trans2 disassoc . trans2 (trans2 unit) . disassoc
   ≡ Roll . InR . trans2 (trans2 dap) . trans2 (trans2 (trans2 unit)) . trans2 disassoc . disassoc
   ≡ Roll . InR . trans2 (trans2 (dap . trans2 unit)) . trans2 disassoc . disassoc
   -- Induction hypothesis
   ≡ Roll . InR . trans2 (trans2 elim2) . trans2 disassoc . disassoc
   ≡ Roll . InR . trans2 elim2 . disassoc
   ≡ Roll . InR . elim2
  dap . trans2 unit
   ≡ eitherSum (Roll . InL . elim2) (Roll . InL . elim2)
         . distributeRight . trans1 unroll
   ≡ Roll . transSum elim2 elim2 . distributeRight . trans1 unroll
   --        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   ≡ Roll . elim2 . trans1 unroll
   ≡ Roll . unroll . elim2
   ≡ elim2
  ```

* Composition
  
  ```haskell
  dap . trans2 dap
   ≡ eitherSum actG apRecurse . distributeRight . trans1 unroll
       . trans2 dap
   ≡ eitherSum actG apRecurse . distributeRight . trans2 dap . trans1 unroll
   ≡ eitherSum (actG . trans2 dap) (apRecurse . trans2 dap) . distributeRight . trans1 unroll
  dap . trans1 dap . assoc
   ≡ dap . trans1 (eitherSum actG apRecurse . distributeRight . trans1 unroll) . assoc
   ≡ dap . trans1 (eitherSum actG apRecurse . distributeRight) . assoc . trans1 unroll
   ≡ eitherSum actG apRecurse . distributeRight . trans1 unroll
       . trans1 (eitherSum actG apRecurse . distributeRight) . assoc . trans1 unroll
   ≡ eitherSum actG apRecurse . distributeRight
       . trans1 (unroll . eitherSum actG apRecurse) . trans1 distributeRight . assoc . trans1 unroll
   ≡ eitherSum (actG . trans1 (unroll . eitherSum actG apRecurse))
                (apRecurse . trans1 (unroll . eitherSum actG apRecurse))
       . distributeRight . trans1 distributeRight . assoc . trans1 unroll
   ≡ eitherSum (actG . trans1 (unroll . eitherSum actG apRecurse))
                (apRecurse . trans1 (unroll . eitherSum actG apRecurse))
       . transSum assoc assoc . distributeRight . trans1 unroll
   ≡ eitherSum (actG . trans1 (unroll . eitherSum actG apRecurse) . assoc)
                (apRecurse . trans1 (unroll . eitherSum actG apRecurse) . assoc)
       . distributeRight . trans1 unroll
  ```

  Therefore, the following equations combined implies the goal.
  
  * `actG . trans2 dap ≡ actG . trans1 (unroll . eitherSum actG apRecurse) . assoc`
  * `apRecurse . trans2 dap ≡ actG . trans1 (unroll . eitherSum actG apRecurse) . assoc`
  
  Prove each equations.

  * `actG . trans2 dap ≡ actG . trans1 (unroll . eitherSum actG apRecurse) . assoc`

    ```haskell
    actG . trans2 dap
     ≡ actG . trans2 (unroll . dap)
     ≡ actG . trans2 (unroll . eitherSum actG apRecurse . distributeRight . trans1 unroll)
     ≡ actG . trans2 (
           eitherSum actG apRecurse . distributeRight . trans1 unroll
        )
     ≡ actG . trans2 (
           eitherSum
              (Roll . transSum dap (trans1 dap . assoc) . distributeLeft . trans2 unroll)
              (Roll . InR . trans2 (trans2 dap) . trans2 disassoc . disassoc)
            . distributeRight . trans1 unroll
        )
     ≡ actG . trans2 Roll . trans2 (
           eitherSum
              (transSum dap (trans1 dap . assoc) . distributeLeft . trans2 unroll)
              (InR . trans2 (trans2 dap) . trans2 disassoc . disassoc)
            . distributeRight . trans1 unroll
        )
     ≡ -- 力尽きた
    ```

## `liftT` is an applicative transformation
## Universal properties of `ApT`