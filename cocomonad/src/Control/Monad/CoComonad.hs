{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

-- | Monad transformer from @Comonad@.
--
-- This module provides the 'CoT' monad transformer, which adds a "comonadic context"
-- to another monad.
--
-- ==== What does @CoT@ do?
--
-- For any @Comonad f@ and @Monad g@, @CoT f g@ is a monad that combines the original
-- effect of the monad @g@ with the ability to use the comonad @f@ as a context. For example:
--
-- * @CoT ('Env' e) g@ is a monad with the @g@ effect and access to a value of type @e@.
--
--     * This is exactly what @'ReaderT' e g@ provides, and in fact, @CoT (Env e) g@ is isomorphic to
--       @ReaderT e g@: see 'fromReaderT' and 'toReaderT'.
--
-- * @CoT ('Store' s) g@ is a monad with the @g@ effect and access to a context that holds
--   a store of @s@ values, which can be queried or updated.
--
--     * This corresponds exactly to what @'StateT' s g@ provides, and indeed,
--       @CoT (Store s) g@ is isomorphic to @StateT s g@: see 'fromStateT' and 'toStateT'.
--
-- * Similarly, @CoT ('Traced' m) g@ is isomorphic to @'WriterT' m g@.
--
-- The "contextual" effects introduced by @CoT@ can be composed freely. Any nested use of the
-- @CoT@ monad transformer can be flattened into a single layer using the 'Day' functor to
-- combine the contexts:
--
-- @
-- uncurryCoT :: Functor g => CoT f1 (CoT f2 g) ~> CoT (Day f1 f2) g
-- curryCoT   :: Functor g => CoT (Day f1 f2) g ~> CoT f1 (CoT f2 g)
-- @
--
-- ==== Relation to other types
--
-- As a @Functor@, @CoT f g@ is isomorphic to the @'Curried' f g@ type.
-- However, since @Curried@ has an @Applicative@ instance that is not compatible
-- with the @Monad@ instance of @CoT@, a new type was necessary to support the monad
-- behavior described here.
--
-- The non-transformer version, @'Co' f@, is isomorphic to the
-- @'Control.Monad.Co.Co' f@ type from the "Control.Monad.Co" module
-- (which is actually the source of inspiration for this module!).
--
-- The name collision is unfortunate — the author has not yet decided on a final name
-- for this monad transformer. Suggestions are welcome!
--
-- ==== For category theory nerds
-- 
-- The construction of monad @CoT f g@, given @Comonad f@ and @Monad g@,
-- can be explained via Kleisli category.
-- 
-- Recall that providing a @Monad@ instance for a functor @m@ is equivalent to
-- providing a @Category (Kleisli m)@ instance.
--
-- @
-- newtype Kleisli m a b = Kl { runKl :: a -> m b }
-- -- derive @Category (Kleisli m)@ from @Monad m@
-- instance Monad m => Category (Kleisli m) where
--   id :: Kleisli m a a
--   id = Kl return
--   (.) :: Kleisli m b c -> Kleisli m a b -> Kleisli m a c
--   Kl f . Kl g = Kl (f <=< g)
--
-- -- derive @Monad m@ from @Category (Kleisli m)@
-- --   (pseudocode, can't be real Haskell)
-- instance Category (Kleisli m) => Monad m where
--   return = runKl id
--   ma >>= k = runKl (Kl k . Kl (const ma)) ()
-- @
-- 
-- @Kleisli (CoT f g)@ is isomorphic to the following @Arr f g@.
--
-- @
-- type Pair = (,)
-- type Arr f g a b = forall r. Pair a (f r) -> g (Pair b r)
-- @
-- 
-- Here's the transformations showing the isomorphism between @Kleisli (CoT f g)@ and @Arr f g@.
-- 
-- @
-- Kleisli (CoT f g) a b
--  ~ a -> CoT f g b
--  ~ a -> ∀r. f r -> g (b, r)
--  ~ ∀r. a -> f r -> g (b, r)
--  ~ ∀r. (a, f r) -> g (b, r)
--  = ∀r. Pair a (f r) -> g (Pair b r)
--  = Arr f g a b
-- @
-- 
-- @Arr f g@ can be made into @Category@ with the following identity and composition.
-- The @Monad (CoT f g)@ instance is the one derived from this construction.
--
-- @
-- idArr :: (Comonad f, Monad g) => Arr f g a a
-- idArr (a, fr) = pure (a, extract fr)
--
-- compArr :: (Comonad f, Monad g) => Arr f g a b -> Arr f g b c -> Arr f g a c
-- compArr abArr bcArr (a, fr) =
--   abArr (a, duplicate fr) >>= bcArr
-- @
-- 
-- Diagramatically:
-- 
-- > idArr :=
-- >               fmap extract           pure
-- >    Pair a ∘ f --------------> Pair a ------> g ∘ Pair a
-- >
-- > compArr ab bc :=
-- >               fmap duplicate                   ab                   fmap bc                   join
-- >   Pair a ∘ f ----------------> Pair a ∘ f ∘ f ----> g ∘ Pair b ∘ f ---------> g ∘ g ∘ Pair c ------> g ∘ Pair c
-- 
-- Proving category laws for @(idArr, compArr)@ will be simple enough.
module Control.Monad.CoComonad(
  -- * The @CoT@ monad transformer
  CoT(..),

  -- ** Manipulating comonadic part
  contrahoist,
  elimCoT,
  curryCoT,
  uncurryCoT,
  eitherCoT, uneitherCoT,

  -- ** Representing @Reader@, @Writer@, or @State@ effects
  toReaderT, toWriterT, toStateT,
  fromReaderT, fromWriterT, fromStateT,
  asking, telling, stating,

  -- ** Conversion
  toCurried,
  fromCurried,

  -- * Non-transformer version
  type Co,
  co, runCo,
  generalize,
  
  -- | The other @Control.Monad.Co.Co@ monad (in @Control.Monad.Co@ module)
  --   is isomorphic to 'Co' defined here.
  --
  --   @Control.Monad.Co.CoT@ is a kind of @Codensity@ monad with access to some @Comonad@ context,
  --   thus the name.
  toCodensityCo,
  fromCodensityCo,
) where

import Control.Monad
import Data.Functor.Day.Curried (Curried(..))
import FFunctor
import Control.Monad.Morph
import Data.Functor.Identity

import Control.Monad.IO.Class (MonadIO(..))

import Control.Comonad (Comonad(..))
import Control.Comonad.Env (ComonadEnv(..), Env, env)
import Control.Comonad.Traced (ComonadTraced(..), Traced, traced)
import Control.Comonad.Store (ComonadStore(..), Store, store)
import Control.Monad.Trans.Reader (ReaderT(..))
import Control.Monad.Trans.Writer (WriterT (..))
import Control.Monad.Trans.State (StateT (..))
import qualified Control.Monad.Reader.Class as Reader
import qualified Control.Monad.Writer.Class as Writer
import qualified Control.Monad.State.Class as State
import Data.Functor.Day (Day (..))
import Data.Function ((&))
import Data.Functor.Sum (Sum (..))
import Data.Functor.Product (Product (..))
import qualified Control.Monad.Co

-- | @CoT f g@ is a @Monad@ which is based on @Monad g@ but can use @Comonad f@
--   as a context. 
newtype CoT f g a = CoT { runCoT :: forall r. f r -> g (a, r) }
  deriving stock Functor

-- | As a mere @Functor@, @CoT f g@ is isomorphic to @'Curried' f g@.
toCurried :: Functor g => CoT f g ~> Curried f g
toCurried ta = Curried $ \far -> uncurry (&) <$> runCoT ta far

-- | @CoT f g@ is, as mere @Functor@, isomorphic to @'Curried' f g@.
fromCurried :: Functor f => Curried f g ~> CoT f g
fromCurried ca = CoT $ \fr -> runCurried ca (flip (,) <$> fr)

instance (Comonad f, Monad g) => Applicative (CoT f g) where
  pure a = CoT $ \fr -> pure (a, extract fr)
  (<*>) = ap

instance (Comonad f, Monad g) => Monad (CoT f g) where
  ta >>= k = CoT $ \fr -> do
    (a, fr') <- runCoT ta (duplicate fr)
    runCoT (k a) fr'

instance MFunctor (CoT f) where
  hoist :: Monad g => (forall a. g a -> h a) -> CoT f g b -> CoT f h b
  hoist gh (CoT fg) = CoT (gh . fg)

instance (Comonad f) => MonadTrans (CoT f) where
  lift :: Monad g => g a -> CoT f g a
  lift ga = CoT $ \fr -> ( , extract fr) <$> ga

instance (Comonad f, MonadIO g) => MonadIO (CoT f g) where
  liftIO = lift . liftIO


-- | Change of the @Comonad@ part.
--
-- @contrahoist φ@ is a monad morphism @CoT k g ~> CoT f g@ /if/ @φ :: f ~> k@
-- is a comonad morphism.
contrahoist :: (forall x. f x -> k x) -> CoT k g a -> CoT f g a
contrahoist fk (CoT kg) = CoT (kg . fk)

elimCoT :: (Applicative f, Functor g) => CoT f g ~> g
elimCoT ig = fst <$> runCoT ig (pure ())

-- | Nesting of @CoT f1@ and @CoT f2@ can be represented as a single @CoT (Day f1 f2)@ using 
--   'Day' to combine two comonads.
--
-- This is also a /monad isomorphism/. Not only it is an isomorphism,
-- it also keeps its @Monad@ operations @'pure'@ and @('>>=')@.
uncurryCoT :: (Functor g) => CoT f1 (CoT f2 g) ~> CoT (Day f1 f2) g
uncurryCoT tt = CoT $ \(Day f1b f2c op) ->
  (\((a,b),c) -> (a, op b c)) <$> (tt `runCoT` f1b) `runCoT` f2c

-- | The inverse of 'uncurryCo'.
curryCoT :: Functor g => CoT (Day f1 f2) g ~> CoT f1 (CoT f2 g)
curryCoT t = CoT $ \f1b ->
  CoT $ \f2c ->
    (\(a,(b,c)) -> ((a,b),c)) <$> runCoT t (Day f1b f2c (,))

-- * Consuming @Env, Traced, Store@ coeffects === Effects @Reader, Writer, State@

toReaderT :: (Monad g) => CoT (Env e) g a -> ReaderT e g a
toReaderT ta = ReaderT $ \e -> fst <$> runCoT ta (env e ())

toWriterT :: (Monad g) => CoT (Traced m) g a -> WriterT m g a
toWriterT ta = WriterT $ runCoT ta (traced id)

toStateT :: (Monad g) => CoT (Store s) g a -> StateT s g a
toStateT ta = StateT $ \s0 -> runCoT ta (store id s0)

fromReaderT :: (ComonadEnv e f, Monad g) => ReaderT e g a -> CoT f g a
fromReaderT ma = CoT $ \fr -> ( , extract fr) <$> runReaderT ma (ask fr)

fromWriterT :: (ComonadTraced m f, Monad g) => WriterT m g a -> CoT f g a
fromWriterT ma = CoT $ \fr -> (\(a,m) -> (a, trace m fr)) <$> runWriterT ma

fromStateT :: (ComonadStore s f, Monad g) => StateT s g a -> CoT f g a
fromStateT ma = CoT $ \fr ->
  (\(a,s1) -> (a, peek s1 fr)) <$> runStateT ma (pos fr)

asking :: (ComonadEnv e f, Monad g) => CoT f g e
asking = fromReaderT Reader.ask

telling :: (Monoid m, ComonadTraced m f, Monad g) => m -> CoT f g ()
telling m = fromWriterT (Writer.tell m)

stating :: (ComonadStore s f, Monad g) => (s -> (a, s)) -> CoT f g a
stating st = fromStateT (State.state st)

-- * Sum and Product

-- | Product of @CoT@ to the same monad is @CoT@ from sum of comonads.
--
-- Compare it with 'either' function:
-- 
-- @
-- either  :: (a -> c) -> (b -> c) -> (Either a b -> c)
-- either' :: (a -> c, b -> c) -> (Either a b -> c)
-- @
--
-- @eitherCoT@ is a /monad isomorphism/ (witnessed by 'uneitherCoT'.)
eitherCoT :: Product (CoT f1 g) (CoT f2 g) ~> CoT (Sum f1 f2) g
eitherCoT (Pair fg1 fg2) = CoT $ \case
  InL f1 -> runCoT fg1 f1
  InR f2 -> runCoT fg2 f2

-- | The inverse of 'eitherCoT'.
uneitherCoT :: CoT (Sum f1 f2) g ~> Product (CoT f1 g) (CoT f2 g)
uneitherCoT sum2g = Pair (contrahoist InL sum2g) (contrahoist InR sum2g)

-- * Non-transformer version

-- | Non-transformer version of @CoT@.
type Co f = CoT f Identity

co :: (forall r. f r -> (a,r)) -> Co f a
co k = CoT (Identity . k)

runCo :: Co f a -> f r -> (a, r)
runCo c fr = runIdentity $ runCoT c fr

toCodensityCo :: Functor f => Co f ~> Control.Monad.Co.Co f
toCodensityCo c = Control.Monad.Co.co $ \far -> runIdentity $ runCurried (toCurried c) far

fromCodensityCo :: Functor f => Control.Monad.Co.Co f ~> Co f
fromCodensityCo c = fromCurried $ Curried $ \far -> Control.Monad.Co.runCo c ((Identity .) <$> far)