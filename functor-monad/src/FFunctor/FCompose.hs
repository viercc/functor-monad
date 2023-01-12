{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module FFunctor.FCompose where

import FFunctor

type FCompose :: FF -> FF -> FF
newtype FCompose ff gg h x = FCompose {getFCompose :: ff (gg h) x}
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (FFunctor ff, FFunctor gg) => FFunctor (FCompose ff gg) where
  ffmap gh = FCompose . ffmap (ffmap gh) . getFCompose

-- Infix operator synonym
type (⊚) = FCompose

infixl 7 ⊚
