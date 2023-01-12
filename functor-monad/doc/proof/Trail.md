|Status|Confirmed ver|
|----|----|
|Stub| |

# About `Control.Monad.Trail`

## Definitions

```haskell
newtype Trail mm a = Trail {runTrail :: mm ((,) a) ()}

instance (FFunctor mm) => Functor (Trail mm) where
  fmap f = Trail . ffmap (first f) . runTrail

instance (FMonad mm) => Applicative (Trail mm) where
  pure a = Trail $ fpure (a, ())
  (<*>) = ap

instance (FMonad mm) => Monad (Trail mm) where
  ma >>= k = Trail . fjoin . ffmap (plug . first (runTrail . k)) . runTrail $ ma
  {-
  join mma
    = mma >>= id
    = Trail . fjoin . ffmap (plug . first (runTrail . id)) . runTrail $ mma
    = Trail . fjoin . ffmap (plug . first runTrail) . runTrail $ mma
  
  join = Trail . fjoin . ffmap (plug . first runTrail) . runTrail
  -}

plug :: forall f x. Functor f => (f (), x) -> f x
plug (f_, a) = a <$ f_
```

## `Trail` is a lawful `Monad`

To reduce bothersome `newtype` wrapping/unwrapping, instead of dealing with `pure` and `join`,
prove the `Monad` law in terms of the following unwrapped functions.

```haskell
fmap' :: FMonad mm => (a -> b) -> mm ((,) a) () -> mm ((,) b) ()
fmap' f = ffmap (first f)

pure' :: FMonad mm => a -> mm ((,) a) ()
pure' = fpure . (, ())

join' :: FMonad mm => mm ((,) (mm ((,) a) ()) () -> mm ((,) a) ()
join' = fjoin . ffmap plug
```

* Lemma [plugunit]

  ```haskell
  -- (1)
  plug . (, ())
   = \f_ -> () <$ f_
   = \f_ -> (const () :: () -> ()) <$> f_
   = \f_ -> id <$> f_
   = id

  -- (2)
  plug . first (, ())
   = \(a,b) -> b <$ (a, ())
   = \(a,b) -> (a,b)
   = id
  ```

* Lemma [plugnat]

  For any natural transformation `n :: f ~> g`,

  ```haskell
  plug . first n :: (f (), b) -> g b
    = \(f_, b) -> b <$ n f_
      -- (b <$) = fmap (const b), and fmap commutes with n
    = \(f_, b) -> n (b <$ f_)
    = n . plug
  ```

  Note that `ffmap _`, `fpure`, and `fjoin` are all natural transformations.

* Left unit:

  ```haskell
  join' . pure'
  = fjoin . ffmap plug . fpure . (, ())
  -- naturality of fpure
  = fjoin . fpure . plug . (, ())
  -- FMonad law
  = plug . (, ())
  -- plugunit(1)
  = id
  ```

* Right unit:

  ```haskell
  join' . fmap' pure'
  = fjoin . ffmap plug . ffmap (first (fpure . (, ())))
  = fjoin . ffmap (plug . first (fpure . (,)))
    -- plugnat
  = fjoin . ffmap (fpure . plug . first (, ()))
  = fjoin . ffmap fpure . ffmap (plug . first (, ()))
    -- FMonad law
  = ffmap (plug . first (, ()))
    -- plugunit(2)
  = ffmap id
  = id
  ```

* Associativity:

  ```haskell
  join' . join'
  = fjoin . ffmap plug . fjoin . ffmap plug
    -- naturality of fjoin
  = fjoin . fjoin . ffmap (ffmap plug) . ffmap plug
  = fjoin . fjoin . ffmap (ffmap plug . plug)

  join' . fmap' join'
  = fjoin . ffmap plug . ffmap (first (fjoin . ffmap plug))
  = fjoin . ffmap (plug . first (fjoin . ffmap plug))
    -- plugnat
  = fjoin . ffmap (fjoin . ffmap plug . plug)
  = fjoin . ffmap fjoin . ffmap (ffmap plug . plug)
    -- FMonad law
  = fjoin . fjoin . ffmap (ffmap plug . plug)
  = join' . join'
  ```

## `Trail (FreeT' m)` is isomorphic to `ListT m` as a `Monad`

TODO
