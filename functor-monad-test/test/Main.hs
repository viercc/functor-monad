{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Hedgehog
import Hedgehog.Main (defaultMain)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Hedgehog.FunctorGen qualified as FGen

import qualified FFunctor.Law as Law

main :: IO ()
main = defaultMain [checkSum]

checkSum :: IO Bool
checkSum = checkParallel $ Group "Sum.FFunctor"
  [
    ("ffmap_id @(Sum Maybe) @List @Int", Law.ffmap_id (FGen.sumFGen FGen.maybeF FGen.listF))
  ]
