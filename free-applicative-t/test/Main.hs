{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)
import Control.Applicative (Const(..), ZipList(..))

import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Expr

import Control.Applicative.Trans.FreeAp

-- Generators
type GenExpr f = forall a. Gen (f (Expr a))

genList :: GenExpr []
genList = Gen.list (Range.linear 0 4) genVar

descList :: [a] -> String
descList as = "List(" ++ show (length as) ++ ")"

genZipList :: GenExpr ZipList
genZipList = ZipList <$> genList

descZipList :: ZipList a -> String
descZipList as = "ZipList(" ++ show (length as) ++ ")"

genMaybe :: GenExpr Maybe
genMaybe = Gen.maybe genVar

descMaybe :: Maybe a -> String
descMaybe = maybe "Nothing" (const "Just _")

genStr :: Gen String
genStr = Gen.string (Range.linear 0 4) (Gen.element "abc")

genConst :: GenExpr (Const String)
genConst = Const <$> genStr

descConst :: Show c => Const c a -> String
descConst = show

genWriter :: GenExpr ((,) String)
genWriter = (,) <$> genStr <*> genVar

descWriter :: Show m => (m, a) -> String
descWriter (m, _) = "(" ++ show m ++ ",_)"

genApT :: GenExpr f -> GenExpr g -> GenExpr (ApT f g)
genApT genF genG = Gen.choice [gen0, gen1, gen2]
  where
    cons genRest = do
        x <- genVar
        ga <- genG
        fb <- genF
        rc <- genRest
        pure $ ApT (\a b c -> x `appE` a `appE` b `appE` c) ga fb rc
    gen0 = PureT <$> genG
    gen1 = cons gen0
    gen2 = cons gen1

descApT :: (forall x. f x -> String) -> (forall x. g x -> String) -> ApT f g a -> String
descApT descF descG as = "ApT[" ++ foldApT_ (\fx -> "," ++ descF fx ++ ",") descG as ++ "]"

-- Testing Applicatives

law_Applicative
    :: (Applicative g, forall c. Eq (g (Expr c)), forall c. Show (g (Expr c)))
    => GroupName -> GenExpr g -> Group
law_Applicative name genG = Group name
    [ ("left unit", left_unit)
    , ("right unit", right_unit)
    , ("associativity", assoc)
    ]
  where
    left_unit = property $ do
        gx <- forAll genG
        (pure id <*> gx) === gx
    right_unit = property $ do
        gx <- forAll genG
        y <- forAll genVar
        (gx |<*>| pure y) === fmap (`appE` y) gx
    assoc = property $ do
        x <- forAll genG
        y <- forAll genG
        z <- forAll genG
        (x |<*>| (y |<*>| z)) === (dotE <$> x <*> y <*> z)
    
    dotE f g a = appE f (appE g a)

law_Applicative_hom
    :: (Applicative f, Applicative g,
        forall c. Show (f (Expr c)),
        forall c. Eq (g (Expr c)), forall c. Show (g (Expr c)))
    => (forall x. f x -> g x) -> GenExpr f -> Property
law_Applicative_hom fg genF = property $ do
    x <- forAll $ genF
    y <- forAll $ genF
    (fg x |<*>| fg y) === fg (x |<*>| y)

-- Lawful Applicative (ApT [] (Writer String))
grp_List_Writer_Applicative_laws :: Group
grp_List_Writer_Applicative_laws =
    law_Applicative "ApT [] (Writer String) - Applicative laws" (genApT genList genWriter)

-- Applicative (ApT [] [])
grp_List_List_Applicative_laws :: Group
grp_List_List_Applicative_laws =
    law_Applicative "ApT [] [] - Applicative laws" (genApT genList genList)

-- Applicative (ApT [] ZipList)
grp_List_ZipList_Applicative_laws :: Group
grp_List_ZipList_Applicative_laws =
    law_Applicative "ApT [] ZipList - Applicative laws" (genApT genList genZipList)

-- | liftT :: [] ~> ApT [] []
prop_hom_liftT_List :: Property
prop_hom_liftT_List = law_Applicative_hom @[] @(ApT [] []) liftT genList

-- | liftT :: (,) String ~> ApT [] ((,) String)
prop_hom_liftT_Writer :: Property
prop_hom_liftT_Writer = law_Applicative_hom @((,) String) @(ApT [] ((,) String)) liftT genWriter

-- | foldApT id id :: ApT [] [] ~> []
prop_hom_foldApT_List_List_List :: Property
prop_hom_foldApT_List_List_List = law_Applicative_hom (foldApT id id) (genApT genList genList)

-- | foldApT ZipList id :: ApT [] ZipList ~> ZipList
prop_hom_foldApT_List_ZipList_ZipList :: Property
prop_hom_foldApT_List_ZipList_ZipList = law_Applicative_hom (foldApT ZipList id) (genApT genList genZipList)

-- | foldApT showLen forgetData :: ApT [] (Writer String) -> Const String
prop_hom_foldApT_List_Writer_Const :: Property
prop_hom_foldApT_List_Writer_Const = law_Applicative_hom (foldApT showLen forgetData) (genApT genList genWriter)

law_foldApT_liftF_liftT ::
     (Traversable f, Eq1 f, Show (f Int), Traversable g, Eq1 g, Show (g Int))
  => Applicative g
  => GenExpr (ApT f g) -> Property
law_foldApT_liftF_liftT gen = property $ do
    x <- forAll gen
    foldApT liftF liftT x === x

prop_foldApT_liftF_liftT_List_List :: Property
prop_foldApT_liftF_liftT_List_List =
    law_foldApT_liftF_liftT (genApT genList genList)

prop_foldApT_liftF_liftT_Maybe_Writer :: Property
prop_foldApT_liftF_liftT_Maybe_Writer = 
    law_foldApT_liftF_liftT (genApT genMaybe genWriter)

prop_foldApT_liftF_liftT_Writer_ZipList :: Property
prop_foldApT_liftF_liftT_Writer_ZipList = 
    law_foldApT_liftF_liftT (genApT genWriter genZipList)

-- | Not an applicative hom
showLen :: Foldable f => f a -> Const String a
showLen = Const . show . length

-- | An applicative hom
forgetData :: (m, x) -> Const m x
forgetData (m,_) = Const m

shouldSuccess :: IO Bool -> IO ()
shouldSuccess m = m >>= \result -> unless result exitFailure

main :: IO ()
main = do
    shouldSuccess $ checkParallel grp_List_Writer_Applicative_laws
    shouldSuccess $ checkParallel grp_List_List_Applicative_laws
    shouldSuccess $ checkParallel grp_List_ZipList_Applicative_laws
    shouldSuccess $ checkParallel $$(discover)

-- Orphan instance
deriving via [] instance Eq1 ZipList