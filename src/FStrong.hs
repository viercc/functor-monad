{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module FStrong where

import Data.Functor.Day
import Data.Functor.Day.Curried
import Data.Functor.Compose

import Data.Coerce ( coerce )

import FFunctor

import Control.Monad.Trans.Identity (IdentityT(..))
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Monad.Trans.State (StateT(..))
import Control.Monad.Trans.Reader (ReaderT(..))

class FFunctor ff => FStrong ff where
    {-# MINIMAL fstrength | mapCurried #-}
    fstrength :: (Functor g) => Day (ff g) h ~> ff (Day g h)
    fstrength (Day ffg h op) =
        runCurried (mapCurried (unapplied h)) (fmap op ffg)

    mapCurried :: (Functor g, Functor h) => Curried g h ~> Curried (ff g) (ff h)
    mapCurried gh = Curried $ \ffg -> ffmap applied (fstrength (Day ffg gh id))

innerAp :: (FStrong ff, Applicative h) => ff h (a -> b) -> h a -> ff h b
innerAp ffh h = ffmap dap $ fstrength (Day ffh h ($))

instance FStrong IdentityT where
    fstrength = coerce

instance FStrong (Day f) where
    fstrength = disassoc

instance Functor f => FStrong (Curried f) where
    fstrength (Day fg h op) = Curried $ \f ->
        let -- fg :: Curried f g b
            -- h :: h c
            -- op :: b -> c -> x
            -- f :: f (x -> r)
            f' = fmap (\k b c -> k (op b c)) f
            -- f' :: f (b -> c -> r)
            g' = runCurried fg f'
            -- g' :: g (c -> r)
        in Day g' h ($)

instance Functor f => FStrong (Compose f) where
    fstrength (Day (Compose fg) h op) = Compose (fmap (\g -> Day g h op) fg)

instance FStrong (ReaderT e) where
    fstrength (Day (ReaderT eg) h op) = ReaderT $ \e -> Day (eg e) h op

instance FStrong (WriterT m) where
    fstrength (Day (WriterT gm) h op) = WriterT $ Day gm h (\(b,m) c -> (op b c, m))

instance FStrong (StateT s) where
    -- StateT s = ReaderT s ∘ WriterT s = Compose ((->) s) ∘ WriterT s
    fstrength (Day (StateT sgs) h op) = StateT $ \s -> Day (sgs s) h (\(b,s') c -> (op b c, s'))

-- TODO: StateT generalizes
--
-- newtype FCompose ff gg f x = FCompose (ff (gg f) x)
-- instance (FStrong ff, FStrong gg) => FStrong (FCompose ff gg)
