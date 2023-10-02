{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE KindSignatures #-}

-- | Composition of two @FFunctor@
module FFunctor.FCompose where

import FFunctor

-- | Composision of @FFunctor@s.
--   Just like any functor, composition of two @FFunctor@ is @FFunctor@ again.
type FCompose :: FF -> FF -> FF
newtype FCompose ff gg h x = FCompose {getFCompose :: ff (gg h) x}
  deriving (Show, Eq, Ord, Foldable, Traversable)

deriving
  via ((ff :: FF) ((gg :: FF) h))
  instance (FFunctor ff, FFunctor gg, Functor h) => Functor (FCompose ff gg h)

instance (FFunctor ff, FFunctor gg) => FFunctor (FCompose ff gg) where
  ffmap gh = FCompose . ffmap (ffmap gh) . getFCompose

-- | Infix type operator for @FCompose@
type (⊚) = FCompose

infixl 7 ⊚
