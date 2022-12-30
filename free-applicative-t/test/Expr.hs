{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
module Expr(Expr(), genVar, appE, (|<$>|), (|<*>|)) where

import Control.Applicative (liftA2)

import Hedgehog ( Gen )
import qualified Hedgehog.Gen as Gen
import Hedgehog.Range ( exponential )

-- Expression
data E = V Int | A E E
    deriving (Eq, Ord)

newtype Expr a = MkExpr E
    deriving (Eq, Ord)

genVar :: Gen (Expr a)
genVar = MkExpr . V <$> Gen.prune (Gen.integral (exponential 0 1000000))

appE :: Expr (a -> b) -> Expr a -> Expr b
appE (MkExpr e1) (MkExpr e2) = MkExpr (A e1 e2)

infixl 9 `appE`

(|<$>|) :: Functor g => Expr (a -> b) -> g (Expr a) -> g (Expr b)
x |<$>| y = fmap (appE x) y

infixl 4 |<$>|

(|<*>|) :: Applicative g => g (Expr (a -> b)) -> g (Expr a) -> g (Expr b)
(|<*>|) = liftA2 appE

infixl 4 |<*>|

instance Show (Expr a) where
    showsPrec p (MkExpr e) = prettyE p e

prettyE :: Int -> E -> ShowS
prettyE _ (V n) = shows n
prettyE p (A e1 e2) = showParen (p > 10) (prettyE 10 e1 . (' ':) . prettyE 11 e2)
