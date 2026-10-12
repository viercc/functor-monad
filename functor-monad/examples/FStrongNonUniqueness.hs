{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module FStrongNonUniqueness where

import Data.Functor.Day(Day(..))
import Data.Functor.Day.Curried
import FFunctor
import FStrong
import Data.Functor ((<&>))
import FMonad (FMonad (..))

-- * Stamping action on functor and its relation to 'Curried'

newtype Stamp a h r = Stamp {unStamp :: h (r,a)}
  deriving (Functor, Foldable, Traversable)

eps :: (a -> r, a) -> r
eps = uncurry ($)

runCurried' :: (Functor g) => Curried g h a -> (g ~> Stamp a h)
runCurried' (Curried gh) gr = Stamp $ gh ((,) <$> gr)

mkCurried' :: (Functor h) => (g ~> Stamp a h) -> Curried g h a
mkCurried' gh = Curried $ \gar -> eps <$> unStamp (gh gar)

unitStamp :: (Functor h) => Stamp () h ~> h
unitStamp = fmap fst . unStamp

unitStamp' :: (Functor h) => h ~> Stamp () h
unitStamp' = Stamp . fmap (,())

assocStamp :: (Functor h) => Stamp (a,b) h ~> Stamp a (Stamp b h)
assocStamp = Stamp . Stamp . fmap (\(x,(a,b)) -> ((x,a),b)) . unStamp

assocStamp' :: (Functor h) => Stamp a (Stamp b h) ~> Stamp (a,b) h
assocStamp' = Stamp . fmap (\((x,a),b) -> (x,(a,b))) . unStamp . unStamp

instance FFunctor (Stamp a) where
  ffmap fg = Stamp . fg . unStamp

-- * FStrong is equivalent to Hop

-- | Moves 'Stamp' out.
--
-- **Laws**
--
-- > hop . ffmap unitStamp' = unitStamp'
--
-- > hop . ffmap assocStamp' = assocStamp' . ffmap hop . hop
class (FFunctor ff) => Hop ff where
  hop :: (Functor h) => ff (Stamp a h) ~> Stamp a (ff h)

hopDefault :: (FStrong ff, Functor h) => ff (Stamp a h) ~> Stamp a (ff h)
hopDefault = runCurried' (mapCurried (mkCurried' id))

mapCurriedDefault ::
  (Hop ff, Functor g, Functor h) =>
  Curried g h ~> Curried (ff g) (ff h)
mapCurriedDefault gh = mkCurried' (hop . ffmap (runCurried' gh))

fstrengthDefault ::
  (Hop ff, Functor g) =>
  Day (ff g) h ~> ff (Day g h)
fstrengthDefault (Day ffg h op) = fmap (uncurry op) . unStamp $ hop (ffmap (`stampDay` h) ffg)

stampDay :: g a -> h b -> Stamp b (Day g h) a
stampDay g h = Stamp $ Day g h (,)

-- * An example instance with multiple Hop instance

-- ** Dup

newtype Dup f a = Dup { runDup :: f (f a)}
  deriving (Functor)

deriving instance Show (f (f a)) => Show (Dup f a)

instance FFunctor Dup where
  ffmap gh = Dup . fmap gh . gh . runDup

instance Hop Dup where
  hop = hop1

-- | There are two valid instances of @Hop Dup@
hop1, hop2 :: Functor h => Dup (Stamp a h) ~> Stamp a (Dup h)
hop1 (Dup shsh) = Stamp . Dup $ unStamp shsh <&> \(sh, a0) -> unStamp sh <&> \(x,_) -> (x,a0)
hop2 (Dup shsh) = Stamp . Dup $ unStamp shsh <&> \(sh, _)  -> unStamp sh <&> \(x,a1) -> (x,a1)


-- ** Free1

-- | Free Bind (Bind = Monad sans pure)
data Free1 f a = Lift (f a) | Wrap1 (f (Free1 f a))
  deriving Functor

join1 :: Functor f => Free1 f (Free1 f a) -> Free1 f a
join1 (Lift fma) = Wrap1 fma
join1 (Wrap1 fmma) = Wrap1 (fmap join1 fmma)

instance FFunctor Free1 where
  ffmap gh (Lift ga) = Lift (gh ga)
  ffmap gh (Wrap1 gma) = Wrap1 (fmap (ffmap gh) (gh gma))

instance FMonad Free1 where
  fpure = Lift
  fbind k (Lift ga) = k ga
  fbind k (Wrap1 gma) = join1 $ k (fmap (fbind k) gma)

instance FStrong Free1 where
  fstrength = fstrengthDefault

instance Hop Free1 where
  hop = hopLast

-- "Take Last" hopping
hopLast :: Functor h => Free1 (Stamp a h) ~> Stamp a (Free1 h)
hopLast (Lift sh) = Stamp . Lift $ unStamp sh
hopLast (Wrap1 shmx) = Stamp . Wrap1 $ unStamp shmx <&> \(mx, _) -> unStamp (hopLast mx)

-- "Take First" hopping
hopFirst :: Functor h => Free1 (Stamp a h) ~> Stamp a (Free1 h)
hopFirst (Lift sh) = Stamp . Lift . unStamp $ sh
hopFirst (Wrap1 shmx) = Stamp . Wrap1 $ unStamp shmx <&> \(mx,a) -> go a mx
  where
    go :: Functor g => a -> Free1 (Stamp b g) x -> Free1 g (x,a)
    go a0 (Lift sg) = Lift . fmap (a0 <$) . unStamp $ sg
    go a0 (Wrap1 sgmx) = Wrap1 $ unStamp sgmx <&> \(mx, _) -> go a0 mx

-- "Take Second If Exist" hopping
hopSecond :: Functor h => Free1 (Stamp a h) ~> Stamp a (Free1 h)
hopSecond (Lift sh) = Stamp . Lift . unStamp $ sh
hopSecond (Wrap1 shmx) = Stamp . Wrap1 $ unStamp shmx <&> \(mx,_) -> unStamp (hopFirst mx)