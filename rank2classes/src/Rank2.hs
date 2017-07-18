-- | Import this module qualified, like this:
-- 
-- > import qualified Rank2
-- 
-- This will bring into scope the standard classes 'Functor', 'Applicative', 'Foldable', and 'Traversable', but with a
-- @Rank2.@ prefix and a twist that their methods operate on a heterogenous collection. The same property is shared by
-- the two less standard classes 'Apply' and 'Distributive'.
{-# LANGUAGE InstanceSigs, KindSignatures, Rank2Types, ScopedTypeVariables, PolyKinds, DefaultSignatures #-}
module Rank2 (
-- * Rank 2 classes
   Functor(..), Apply(..), Applicative(..),
   Foldable(..), Traversable(..), Distributive(..), DistributiveTraversable(..), distributeM,
-- * Rank 2 data types
   Compose(..), Empty(..), Only(..), Identity(..), Product(..), Arrow(..),
-- * Method synonyms and helper functions
   ap, fmap, liftA3, liftA4, liftA5,
   fmapTraverse, liftA2Traverse1, liftA2Traverse2, liftA2TraverseBoth,
   cotraverse, cotraverseTraversable)
where

import qualified Control.Applicative as Rank1
import qualified Control.Monad as Rank1
import qualified Data.Foldable as Rank1
import qualified Data.Traversable as Rank1
import Data.Monoid (Monoid(..), (<>))
import Data.Functor.Compose (Compose(..))

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

-- | Equivalent of 'Functor' for rank 2 data types
class Functor g where
   (<$>) :: (forall a. p a -> q a) -> g p -> g q

-- | Alphabetical synonym for '<$>'
fmap :: Functor g => (forall a. p a -> q a) -> g p -> g q
fmap f g = f <$> g
{-# INLINE fmap #-}

-- | Equivalent of 'Foldable' for rank 2 data types
class Foldable g where
   foldMap :: Monoid m => (forall a. p a -> m) -> g p -> m

-- | Equivalent of 'Traversable' for rank 2 data types
class (Functor g, Foldable g) => Traversable g where
   {-# MINIMAL traverse | sequence #-}
   traverse :: Rank1.Applicative m => (forall a. p a -> m (q a)) -> g p -> m (g q)
   sequence :: Rank1.Applicative m => g (Compose m p) -> m (g p)
   traverse f = sequence . fmap (Compose . f)
   sequence = traverse getCompose

-- | Wrapper for functions that map the argument constructor type
newtype Arrow p q a = Arrow{apply :: p a -> q a}

-- | Subclass of 'Functor' halfway to 'Applicative'
--
-- > (.) <$> u <*> v <*> w == u <*> (v <*> w)
class Functor g => Apply g where
   {-# MINIMAL liftA2 | (<*>) #-}
   -- | Equivalent of 'Rank1.<*>' for rank 2 data types
   (<*>) :: g (Arrow p q) -> g p -> g q
   -- | Equivalent of 'Rank1.liftA2' for rank 2 data types
   liftA2 :: (forall a. p a -> q a -> r a) -> g p -> g q -> g r
   -- | Equivalent of 'Rank1.liftA3' for rank 2 data types
   liftA3 :: (forall a. p a -> q a -> r a -> s a) -> g p -> g q -> g r -> g s

   (<*>) = liftA2 apply
   liftA2 f g h = (Arrow . f) <$> g <*> h
   liftA3 f g h i = liftA2 (\p q-> Arrow (f p q)) g h <*> i

liftA4 :: Apply g => (forall a. p a -> q a -> r a -> s a -> t a) -> g p -> g q -> g r -> g s -> g t
liftA4 f g h i j = liftA3 (\p q r-> Arrow (f p q r)) g h i <*> j

liftA5 :: Apply g => (forall a. p a -> q a -> r a -> s a -> t a -> u a) -> g p -> g q -> g r -> g s -> g t -> g u
liftA5 f g1 g2 g3 g4 g5 = liftA4 (\p q r s-> Arrow (f p q r s)) g1 g2 g3 g4 <*> g5

-- | Alphabetical synonym for '<*>'
ap :: Apply g => g (Arrow p q) -> g p -> g q
ap = (<*>)

-- | Equivalent of 'Rank1.Applicative' for rank 2 data types
class Apply g => Applicative g where
   pure :: (forall a. f a) -> g f
  
-- | Equivalent of 'Rank1.Distributive' for rank 2 data types
class DistributiveTraversable g => Distributive g where
   {-# MINIMAL distributeWith #-}
   collect :: Rank1.Functor f1 => (a -> g f2) -> f1 a -> g (Compose f1 f2)
   distribute :: Rank1.Functor f1 => f1 (g f2) -> g (Compose f1 f2)
   distributeWith :: Rank1.Functor f1 => (forall x. f1 (f2 x) -> f x) -> f1 (g f2) -> g f

   collect f = distribute . Rank1.fmap f
   distribute = distributeWith Compose

-- | A weaker 'Distributive' that requires 'Rank1.Traversable' to use, not just a 'Rank1.Functor'.
class Functor g => DistributiveTraversable (g :: (k -> *) -> *) where
   collectTraversable :: Rank1.Traversable f1 => (a -> g f2) -> f1 a -> g (Compose f1 f2)   
   distributeTraversable :: Rank1.Traversable f1 => f1 (g f2) -> g (Compose f1 f2)
   distributeWithTraversable :: Rank1.Traversable f1 => (forall x. f1 (f2 x) -> f x) -> f1 (g f2) -> g f

   collectTraversable f = distributeTraversable . Rank1.fmap f
   distributeTraversable = distributeWithTraversable Compose
   
   default distributeWithTraversable :: (Rank1.Traversable f1, Distributive g) => 
                                        (forall x. f1 (f2 x) -> f x) -> f1 (g f2) -> g f
   distributeWithTraversable = distributeWith

distributeM :: (Distributive g, Rank1.Monad f) => f (g f) -> g f
distributeM = distributeWith Rank1.join

-- | Like 'fmap', but traverses over its argument
fmapTraverse :: (DistributiveTraversable f, Rank1.Traversable g) => (forall a. g (t a) -> u a) -> g (f t) -> f u
fmapTraverse f x = fmap (f . getCompose) (distributeTraversable x)

-- | Like 'liftA2', but traverses over its first argument
liftA2Traverse1 :: (Apply f, DistributiveTraversable f, Rank1.Traversable g) =>
                   (forall a. g (t a) -> u a -> v a) -> g (f t) -> f u -> f v
liftA2Traverse1 f x = liftA2 (f . getCompose) (distributeTraversable x)

-- | Like 'liftA2', but traverses over its second argument
liftA2Traverse2 :: (Apply f, DistributiveTraversable f, Rank1.Traversable g) => 
                   (forall a. t a -> g (u a) -> v a) -> f t -> g (f u) -> f v
liftA2Traverse2 f x y = liftA2 (\x' y' -> f x' (getCompose y')) x (distributeTraversable y)

-- | Like 'liftA2', but traverses over both its arguments
liftA2TraverseBoth :: (Apply f, DistributiveTraversable f, Rank1.Traversable g1, Rank1.Traversable g2) =>
                      (forall a. g1 (t a) -> g2 (u a) -> v a) -> g1 (f t) -> g2 (f u) -> f v
liftA2TraverseBoth f x y = liftA2 applyCompose (distributeTraversable x) (distributeTraversable y)
   where applyCompose x' y' = f (getCompose x') (getCompose y')

-- | Equivalent of 'Rank1.cotraverse' for rank 2 data types 
cotraverse :: (Distributive g, Rank1.Functor f) => (forall i. f (a i) -> b i) -> f (g a) -> g b
cotraverse f = (fmap (f . getCompose)) . distribute

-- | Equivalent of 'Rank1.cotraverse' for rank 2 data types using traversable
cotraverseTraversable :: (DistributiveTraversable g, Rank1.Traversable f) => 
                         (forall i. f (a i) -> b i) -> f (g a) -> g b
cotraverseTraversable f = (fmap (f . getCompose)) . distributeTraversable

-- | A rank-2 equivalent of '()', a zero-element tuple
data Empty f = Empty deriving (Eq, Ord, Show)

-- | A rank-2 tuple of only one element
newtype Only a f = Only {fromOnly :: f a} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Identity' for rank 2 data types
newtype Identity g f = Identity {runIdentity :: g f} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Product' for rank 2 data types
data Product g h f = Pair {fst :: g f, snd :: h f}
                               deriving (Eq, Ord, Show)

newtype Flip g a f = Flip (g (f a)) deriving (Eq, Ord, Show)

instance Monoid (g (f a)) => Monoid (Flip g a f) where
   mempty = Flip mempty
   Flip x `mappend` Flip y = Flip (x `mappend` y)

instance Rank1.Functor g => Rank2.Functor (Flip g a) where
   f <$> Flip g = Flip (f Rank1.<$> g)

instance Rank1.Applicative g => Rank2.Apply (Flip g a) where
   Flip g <*> Flip h = Flip (apply Rank1.<$> g Rank1.<*> h)

instance Rank1.Applicative g => Rank2.Applicative (Flip g a) where
   pure f = Flip (Rank1.pure f)

instance Rank1.Foldable g => Rank2.Foldable (Flip g a) where
   foldMap f (Flip g) = Rank1.foldMap f g

instance Rank1.Traversable g => Rank2.Traversable (Flip g a) where
   traverse f (Flip g) = Flip Rank1.<$> Rank1.traverse f g

instance Functor Empty where
   _ <$> _ = Empty

instance Functor (Only a) where
   f <$> Only a = Only (f a)

instance Functor g => Functor (Identity g) where
   f <$> Identity g = Identity (f <$> g)

instance (Functor g, Functor h) => Functor (Product g h) where
   f <$> g = Pair (f <$> fst g) (f <$> snd g)

instance Foldable Empty where
   foldMap _ _ = mempty

instance Foldable (Only x) where
   foldMap f (Only x) = f x

instance Foldable g => Foldable (Identity g) where
   foldMap f (Identity g) = foldMap f g

instance (Foldable g, Foldable h) => Foldable (Product g h) where
   foldMap f ~(Pair g h) = foldMap f g <> foldMap f h

instance Traversable Empty where
   traverse _ _ = Rank1.pure Empty

instance Traversable (Only x) where
   traverse f (Only x) = Only Rank1.<$> f x

instance Traversable g => Traversable (Identity g) where
   traverse f (Identity g) = Identity Rank1.<$> traverse f g

instance (Traversable g, Traversable h) => Traversable (Product g h) where
   traverse f ~(Pair g h) = Rank1.liftA2 Pair (traverse f g) (traverse f h)

instance Apply Empty where
   _ <*> _ = Empty
   liftA2 _ _ _ = Empty

instance Apply (Only x) where
   Only f <*> Only x = Only (apply f x)
   liftA2 f (Only x) (Only y) = Only (f x y)

instance Apply g => Apply (Identity g) where
   Identity g <*> Identity h = Identity (g <*> h)
   liftA2 f (Identity g) (Identity h) = Identity (liftA2 f g h)

instance (Apply g, Apply h) => Apply (Product g h) where
   gf <*> gx = Pair (fst gf <*> fst gx) (snd gf <*> snd gx)
   liftA2 f ~(Pair g1 g2) ~(Pair h1 h2) = Pair (liftA2 f g1 h1) (liftA2 f g2 h2)

instance Applicative Empty where
   pure = const Empty

instance Applicative (Only x) where
   pure = Only

instance Applicative g => Applicative (Identity g) where
   pure f = Identity (pure f)

instance (Applicative g, Applicative h) => Applicative (Product g h) where
   pure f = Pair (pure f) (pure f)

instance DistributiveTraversable Empty
instance DistributiveTraversable (Only x)
instance DistributiveTraversable g => DistributiveTraversable (Identity g) where
   distributeWithTraversable w f = Identity (distributeWithTraversable w $ Rank1.fmap runIdentity f)
instance (DistributiveTraversable g, DistributiveTraversable h) => DistributiveTraversable (Product g h) where
   distributeWithTraversable w f = Pair (distributeWithTraversable w $ Rank1.fmap fst f) 
                                        (distributeWithTraversable w $ Rank1.fmap snd f)

instance Distributive Empty where
   distributeWith _ _ = Empty

instance Distributive (Only x) where
   distributeWith w f = Only (w $ Rank1.fmap fromOnly f)

instance Distributive g => Distributive (Identity g) where
   distributeWith w f = Identity (distributeWith w $ Rank1.fmap runIdentity f)

instance (Distributive g, Distributive h) => Distributive (Product g h) where
   distributeWith w f = Pair (distributeWith w $ Rank1.fmap fst f) (distributeWith w $ Rank1.fmap snd f)

