{-# LANGUAGE PolyKinds #-}
module Data.Bifunctor.Product.Extra where

import Data.Bifunctor.Product

proj1 :: Product p q a b -> p a b
proj1 (Pair p _) = p

proj2 :: Product p q a b -> q a b
proj2 (Pair _ q) = q
