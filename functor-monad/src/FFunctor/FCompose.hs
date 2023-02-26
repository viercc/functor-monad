{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE KindSignatures #-}

module FFunctor.FCompose where

import FFunctor

type FCompose :: FF -> FF -> FF
newtype FCompose ff gg h x = FCompose {getFCompose :: ff (gg h) x}
  deriving (Show, Eq, Ord, Foldable, Traversable)

deriving
  via ((ff :: FF) ((gg :: FF) h))
  instance (FFunctor ff, FFunctor gg, Functor h) => Functor (FCompose ff gg h)

instance (FFunctor ff, FFunctor gg) => FFunctor (FCompose ff gg) where
  ffmap gh = FCompose . ffmap (ffmap gh) . getFCompose

-- | Infix operator synonym
type (⊚) = FCompose

infixl 7 ⊚
