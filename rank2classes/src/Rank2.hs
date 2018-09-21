-- | Import this module qualified, like this:
-- 
-- > import qualified Rank2
-- 
-- This will bring into scope the standard classes 'Functor', 'Applicative', 'Foldable', and 'Traversable', but with a
-- @Rank2.@ prefix and a twist that their methods operate on a heterogenous collection. The same property is shared by
-- the two less standard classes 'Apply' and 'Distributive'.
{-# LANGUAGE DefaultSignatures, InstanceSigs, KindSignatures, PolyKinds, Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators #-}
module Rank2 (
-- * Rank 2 classes
   Functor(..), Apply(..), Applicative(..),
   Foldable(..), Traversable(..), Distributive(..), DistributiveTraversable(..), distributeJoin,
-- * Rank 2 data types
   Compose(..), Empty(..), Only(..), Identity(..), Product(..), Sum(..), Arrow(..), type (~>),
-- * Method synonyms and helper functions
   fst, snd, ap, fmap, liftA4, liftA5,
   fmapTraverse, liftA2Traverse1, liftA2Traverse2, liftA2TraverseBoth,
   distributeWith, distributeWithTraversable)
where

import qualified Control.Applicative as Rank1
import qualified Control.Monad as Rank1
import qualified Data.Foldable as Rank1
import qualified Data.Traversable as Rank1
import Data.Coerce (coerce)
import Data.Semigroup (Semigroup(..))
import Data.Monoid (Monoid(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Sum (Sum(..))

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

-- | Helper function for accessing the first field of a 'Pair'
fst :: Product g h p -> g p
fst (Pair x _) = x

-- | Helper function for accessing the second field of a 'Pair'
snd :: Product g h p -> h p
snd (Pair _ y) = y

-- | Equivalent of 'Functor' for rank 2 data types, satisfying the usual functor laws
--
-- > id <$> g == g
-- > (p . q) <$> g == p <$> (q <$> g)
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

type (~>) = Arrow
infixr 0 ~>

-- | Subclass of 'Functor' halfway to 'Applicative', satisfying
--
-- > (.) <$> u <*> v <*> w == u <*> (v <*> w)
class Functor g => Apply g where
   {-# MINIMAL liftA2 | (<*>) #-}
   -- | Equivalent of 'Rank1.<*>' for rank 2 data types
   (<*>) :: g (p ~> q) -> g p -> g q
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
ap :: Apply g => g (p ~> q) -> g p -> g q
ap = (<*>)

-- | Equivalent of 'Rank1.Applicative' for rank 2 data types
class Apply g => Applicative g where
   pure :: (forall a. f a) -> g f

-- | Equivalent of 'Rank1.Distributive' for rank 2 data types
class DistributiveTraversable g => Distributive g where
   {-# MINIMAL cotraverse|distribute #-}
   collect :: Rank1.Functor f1 => (a -> g f2) -> f1 a -> g (Compose f1 f2)
   distribute :: Rank1.Functor f1 => f1 (g f2) -> g (Compose f1 f2)
   -- | Dual of 'traverse', equivalent of 'Rank1.cotraverse' for rank 2 data types 
   cotraverse :: Rank1.Functor m => (forall a. m (p a) -> q a) -> m (g p) -> g q

   collect f = distribute . Rank1.fmap f
   distribute = cotraverse Compose
   cotraverse f = (fmap (f . getCompose)) . distribute

-- | A weaker 'Distributive' that requires 'Rank1.Traversable' to use, not just a 'Rank1.Functor'.
class Functor g => DistributiveTraversable (g :: (k -> *) -> *) where
   collectTraversable :: Rank1.Traversable f1 => (a -> g f2) -> f1 a -> g (Compose f1 f2)   
   distributeTraversable :: Rank1.Traversable f1 => f1 (g f2) -> g (Compose f1 f2)
   cotraverseTraversable :: Rank1.Traversable f1 => (forall x. f1 (f2 x) -> f x) -> f1 (g f2) -> g f

   collectTraversable f = distributeTraversable . Rank1.fmap f
   distributeTraversable = cotraverseTraversable Compose
   
   default cotraverseTraversable :: (Rank1.Traversable m, Distributive g) => 
                                    (forall a. m (p a) -> q a) -> m (g p) -> g q
   cotraverseTraversable = cotraverse

-- | A variant of 'distribute' convenient with 'Rank1.Monad' instances
distributeJoin :: (Distributive g, Rank1.Monad f) => f (g f) -> g f
distributeJoin = cotraverse Rank1.join

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

{-# DEPRECATED distributeWith "Use cotraverse instead." #-}
-- | Synonym for 'cotraverse'
distributeWith :: (Distributive g, Rank1.Functor f) => (forall i. f (a i) -> b i) -> f (g a) -> g b
distributeWith = cotraverse

{-# DEPRECATED distributeWithTraversable "Use cotraverseTraversable instead." #-}
-- | Synonym for 'cotraverseTraversable'
distributeWithTraversable :: (DistributiveTraversable g, Rank1.Traversable m) =>
                             (forall a. m (p a) -> q a) -> m (g p) -> g q
distributeWithTraversable = cotraverseTraversable

-- | A rank-2 equivalent of '()', a zero-element tuple
data Empty f = Empty deriving (Eq, Ord, Show)

-- | A rank-2 tuple of only one element
newtype Only a f = Only {fromOnly :: f a} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Identity' for rank 2 data types
newtype Identity g f = Identity {runIdentity :: g f} deriving (Eq, Ord, Show)

newtype Flip g a f = Flip (g (f a)) deriving (Eq, Ord, Show)

instance Semigroup (g (f a)) => Semigroup (Flip g a f) where
   Flip x <> Flip y = Flip (x <> y)

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

instance Functor (Const a) where
   _ <$> Const a = Const a

instance Functor (Only a) where
   f <$> Only a = Only (f a)

instance Functor g => Functor (Identity g) where
   f <$> Identity g = Identity (f <$> g)

instance (Functor g, Functor h) => Functor (Product g h) where
   f <$> ~(Pair a b) = Pair (f <$> a) (f <$> b)

instance (Functor g, Functor h) => Functor (Sum g h) where
   f <$> InL g = InL (f <$> g)
   f <$> InR h = InR (f <$> h)

instance Foldable Empty where
   foldMap _ _ = mempty

instance Foldable (Const x) where
   foldMap _ _ = mempty

instance Foldable (Only x) where
   foldMap f (Only x) = f x

instance Foldable g => Foldable (Identity g) where
   foldMap f (Identity g) = foldMap f g

instance (Foldable g, Foldable h) => Foldable (Product g h) where
   foldMap f ~(Pair g h) = foldMap f g `mappend` foldMap f h

instance (Foldable g, Foldable h) => Foldable (Sum g h) where
   foldMap f (InL g) = foldMap f g
   foldMap f (InR h) = foldMap f h

instance Traversable Empty where
   traverse _ _ = Rank1.pure Empty

instance Traversable (Const x) where
   traverse _ (Const x) = Rank1.pure (Const x)

instance Traversable (Only x) where
   traverse f (Only x) = Only Rank1.<$> f x

instance Traversable g => Traversable (Identity g) where
   traverse f (Identity g) = Identity Rank1.<$> traverse f g

instance (Traversable g, Traversable h) => Traversable (Product g h) where
   traverse f ~(Pair g h) = Rank1.liftA2 Pair (traverse f g) (traverse f h)

instance (Traversable g, Traversable h) => Traversable (Sum g h) where
   traverse f (InL g) = InL Rank1.<$> traverse f g
   traverse f (InR h) = InR Rank1.<$> traverse f h

instance Apply Empty where
   _ <*> _ = Empty
   liftA2 _ _ _ = Empty

instance Semigroup x => Apply (Const x) where
   Const x <*> Const y = Const (x <> y)
   liftA2 _ (Const x) (Const y) = Const (x <> y)

instance Apply (Only x) where
   Only f <*> Only x = Only (apply f x)
   liftA2 f (Only x) (Only y) = Only (f x y)

instance Apply g => Apply (Identity g) where
   Identity g <*> Identity h = Identity (g <*> h)
   liftA2 f (Identity g) (Identity h) = Identity (liftA2 f g h)

instance (Apply g, Apply h) => Apply (Product g h) where
   ~(Pair gf hf) <*> ~(Pair gx hx) = Pair (gf <*> gx) (hf <*> hx)
   liftA2 f ~(Pair g1 h1) ~(Pair g2 h2) = Pair (liftA2 f g1 g2) (liftA2 f h1 h2)

instance Applicative Empty where
   pure = const Empty

instance (Semigroup x, Monoid x) => Applicative (Const x) where
   pure = const (Const mempty)

instance Applicative (Only x) where
   pure = Only

instance Applicative g => Applicative (Identity g) where
   pure f = Identity (pure f)

instance (Applicative g, Applicative h) => Applicative (Product g h) where
   pure f = Pair (pure f) (pure f)

instance DistributiveTraversable Empty
instance DistributiveTraversable (Only x)
instance DistributiveTraversable g => DistributiveTraversable (Identity g) where
   cotraverseTraversable w f = Identity (cotraverseTraversable w $ Rank1.fmap runIdentity f)
instance (DistributiveTraversable g, DistributiveTraversable h) => DistributiveTraversable (Product g h) where
   cotraverseTraversable w f = Pair (cotraverseTraversable w $ Rank1.fmap fst f) 
                                    (cotraverseTraversable w $ Rank1.fmap snd f)

instance Distributive Empty where
   cotraverse _ _ = Empty

instance Monoid x => DistributiveTraversable (Const x) where
   cotraverseTraversable _ f = coerce (Rank1.fold f)

instance Distributive (Only x) where
   cotraverse w f = Only (w $ Rank1.fmap fromOnly f)

instance Distributive g => Distributive (Identity g) where
   cotraverse w f = Identity (cotraverse w $ Rank1.fmap runIdentity f)

instance (Distributive g, Distributive h) => Distributive (Product g h) where
   cotraverse w f = Pair (cotraverse w $ Rank1.fmap fst f) (cotraverse w $ Rank1.fmap snd f)
