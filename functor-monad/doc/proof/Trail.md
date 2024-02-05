|Status|Confirmed ver|
|----|----|
|✓|0.1.1.0|

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

`Trail (FreeT' m)` is isomorphic to `ListT m` as a `Monad`.

There are several packages doing "ListT done right." I'll pick the definition from
[list-transformer](https://hackage.haskell.org/package/list-transformer-1.0.9/docs/List-Transformer.html) package, and prove the equivalence.

```haskell
newtype ListT m a = ListT { next :: m (Step m a) }
data Step m a = Cons a (ListT m a) | Nil

-- I'll differentiate two "pure"/"join" by suffix "L" and "F".
pureL :: Monad m => a -> ListT m a
pureL = ListT $ pure $ Cons a (ListT (pure Nil))

joinL :: Monad m => ListT m (ListT m a) -> ListT m a
joinL (ListT mStep) = ListT $ mStep >>= \case
   Nil -> pure Nil
   Cons ma rest -> next (ma `appendL` joinL rest)

appendL :: Monad m => ListT m a -> ListT m a -> ListT m a
appendL (ListT mStep) rest = ListT $ mStep >>= \case
   Nil -> next rest
   Cons a ma -> pure $ Cons a (appendL ma rest)  
```

Firstly, they are isomorphic as `Functor`, by the following natural isomorphism.

```haskell
-- Underlying representation of Trail (FreeT' m)
newtypeWrapping :: Coercion (FreeT ((,) a) m ()) (Trail (FreeT' m) a)
newtypeWrapping = Coercion

iso1 :: Functor m => ListT m a -> FreeT ((,) a) m ()
iso1 (ListT mStep) = FreeT $ isoStep <$> mStep
  where
    isoStep Nil = Pure ()
    isoStep (Cons a r) = Free (a, iso1 r)

iso2 :: Functor m => FreeT ((,) a) m () -> ListT m a
iso2 (FreeT mf) = ListT $ isoStep' <$> mf
  where
    isoStep' (Pure ()) = Nil
    isoStep' (Free (a, rest)) = Cons a (iso2 rest)

(iso1 . iso2) (FreeT mf)
  = FreeT $ (isoStep . isoStep' <$> mf)
      where
        isoStep Nil = Pure ()
        isoStep (Cons a r) = Free (a, iso1 r)

        isoStep' (Pure ()) = Nil
        isoStep' (Free (a, rest)) = Cons a (iso2 rest)
 = FreeT $ step <$> mf
     where
       step (Pure ()) = Pure ()
       step (Free (a, rest)) = Free (a, (iso1 . iso2) rest)
 = FreeT mf

-- With the mostly same argument:
(iso2 . iso1) = id
```

To prove that `iso1` preserves `Monad` operations,
explicitly spell out `pure` and `join` on `FreeT ((,) a) m ()`,
the underlying data of `Trail (FreeT' m)`.

```haskell
pureF :: a -> FreeT ((,) a) m ()
pureF a = FreeT . pure $ Free (a, pure ())

joinF :: FreeT ((,) (FreeT ((,) a) m ())) m () -> FreeT ((,) a) m ()
joinF = fjoin_ . transFreeT_ plug
  = eitherFreeT_ id inr . transFreeT_ plug
  = eitherFreeT_ plug inr

joinF (FreeT mf) = do
  v <- inr (runFreeT (FreeT mf))
  case v of
    Pure a -> return a
    Free fm -> plug fm >>= joinF
joinF (FreeT mf) = do
  v <- FreeF (fmap Pure <$> mf)
  case v of
    Pure a -> return a
    Free fm -> plug fm >>= joinF
joinF (FreeT mf) = FreeT $ mf >>= \v ->
  case v of
    -- Since @a :: ()@, the only value @a@ will take is ()
    Pure () -> next (return ())
    Free (as, rest) -> next $ (rest <$ as) >>= joinF
joinF (FreeT mf) = FreeT $ mf >>= \v ->
  case v of
    Pure () -> pure (Pure ())
    Free (as, rest) -> next $ as >> joinF rest
```

The isomorphism `iso1` preserves `Monad` operations of `ListT m` to the `(pureF, joinF)` pair.
`pure` part is easy:

```haskell
iso1 (pureL a)
 = iso1 (ListT $ pure $ Cons a (ListT (pure Nil)))
 = FreeT $ isoStep <$> (pure $ Cons a (ListT (pure Nil)))
 = FreeT $ pure $ isoStep (Cons a (ListT (pure Nil)))
 = FreeT $ pure $ Free (a, iso1 (ListT (pure Nil)))
 = FreeT $ pure $ Free (a, FreeT $ isoStep <$> pure Nil)
 = FreeT $ pure $ Free (a, FreeT $ pure (Pure ()))
 = FreeT $ pure $ Free (a, pure ())
 = pureF a
```

`iso1` maps `appendL` to `>>`

```haskell
iso1 (m1 `appendL` m2)
 = iso1 $ ListT $ mStep >>= \case
     Nil -> next m2
     Cons a m1' -> pure (Cons a (m1' `appendL` m2))
 = FreeT $ mStep >>= \case
     Nil -> isoStep <$> next m2
     Cons a m1' -> pure $ isoStep (Cons a (m1' `appendL` m2))
 = FreeT $ mStep >>= \case
     Nil -> next (iso1 m2)
     Cons a m1' -> pure $ Free (a, iso (m1' `appendL` m2))

iso1 m1 >> iso1 m2
 = iso1 (ListT mStep) >> iso1 m2
 = FreeT (isoStep <$> mStep) >> iso1 m2
 = FreeT $ (isoStep <$> mStep) >>= \case
     Pure _ -> next (iso1 m2)
     Free (a, as) >> pure $ Free (a, as >> iso1 m2)
 = FreeT $ mStep >>= \v -> case isoStep v of
     Pure _ -> next (iso1 m2)
     Free (a, as) >> pure $ Free (a, as >> iso1 m2)
 = FreeT $ mStep >>= \case
     Nil -> next (iso1 m2)
     Cons a m1' >> pure $ Free (a, iso1 m1' >> iso1 m2)

-- By induction
iso1 (m1 `appendL` m2) = iso1 m1 >> iso1 m2
```

`iso1` preserves `join`:

```haskell
iso1 (joinL (ListT mStep))
 = iso1 $ ListT $ mStep >>= \case -> 
     Nil -> pure Nil
     Cons ma rest -> ma `appendL` joinL rest
 = FreeT $ fmap isoStep $ mStep >>= \case -> 
     Nil -> pure Nil
     Cons ma rest -> next (ma `appendL` joinL rest)
 = FreeT $ fmap isoStep $ mStep >>= \case -> 
     Nil -> pure (isoStep Nil)
     Cons ma rest -> isoStep <$> next (ma `appendL` joinL rest)
 = FreeT $ mStep >>= \case -> 
     Nil -> pure (Pure ())
     Cons ma rest -> next (iso1 (ma `appendL` joinL rest))
 = FreeT $ mStep >>= \case -> 
     Nil -> pure (Pure ())
     Cons ma rest -> next (iso1 ma >> (iso1 . joinL) rest)

joinF . iso1 . fmap iso1 $ ListT mStep
 = joinF . iso1 $ ListT $ mStep >>= \case ->
     Nil -> pure Nil
     Cons ma rest -> pure $ Cons (iso1 ma) (fmap iso1 rest)
 = joinF $ FreeT $ mStep >>= \case ->
     Nil -> isoStep <$> pure Nil
     Cons ma rest -> isoStep <$> (pure $ Cons (iso1 ma) (fmap iso1 rest))
 = joinF $ FreeT $ mStep >>= \case ->
     Nil -> pure (Pure ())
     Cons ma rest -> pure $ Free (iso1 ma, iso1 (fmap iso1 rest))
 = FreeT $ mStep >>= \case ->
     Nil -> pure (Pure ()) >>= \case
       Pure () -> pure (Pure ())
       Free _ -> ...
     Cons ma rest -> (pure $ Free (iso1 ma, iso1 (fmap iso1 rest))) >>= \case
       Pure () -> ...
       Free (ma', rest') -> next (ma' >> joinF rest')
 = FreeT $ mStep >>= \case ->
     Nil -> pure (Pure ())
     Cons ma rest -> next $ iso1 ma >> joinF (iso1 (fmap iso1 rest'))
 = FreeT $ mStep >>= \case ->
     Nil -> pure (Pure ())
     Cons ma rest -> next $ iso1 ma >> (joinF . iso1 . fmap iso1) rest'

-- By induction:

iso1 . joinF = joinF . iso1 . fmap iso1
```