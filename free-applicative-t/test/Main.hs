module Main (main) where

import Data.Foldable (toList)
import Control.Applicative (liftA2)

import Control.Applicative.Trans.FreeAp

shouldEqual :: (Show a, Eq a) => a -> a -> IO ()
shouldEqual actual expected
    | actual == expected = pure ()
    | otherwise = fail $ "actual: " ++ show actual ++ ", expected: " ++ show expected ++ ""

(<+>) :: Applicative f => f Int -> f Int -> f Int
(<+>) = liftA2 (+)

test1 :: ApT [] Maybe Int
test1 = liftF [1000,2000] <+> liftT (Just 300) <+> liftT (Just 40) <+> liftF [5,6]

explainList :: [a] -> String
explainList as = "List(" ++ show (length as) ++ "), "

explainMaybe :: Maybe a -> String
explainMaybe Nothing = "Nothing, "
explainMaybe (Just _) = "Just _, "

main :: IO ()
main = do
    foldApT id toList test1 `shouldEqual` [1345, 1346, 2345, 2346]
    foldApT_ explainList explainMaybe test1 `shouldEqual` "Just _, List(2), Just _, List(2), Just _, "
