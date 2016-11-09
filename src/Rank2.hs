{-# LANGUAGE InstanceSigs, KindSignatures, Rank2Types, ScopedTypeVariables #-}
module Rank2 (Functor(..), Apply(..), Foldable(..), Traversable(..), Reassemblable(..),
              Empty(..), Singleton(..), Identity(..), Product(..), Arrow(..),
             (<$>), (<*>), liftA2, liftA3)
where

import qualified Control.Applicative as Rank1
import Data.Monoid (mempty, (<>))

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

-- | Equivalent of 'Functor' for rank 2 data types
class Functor g where
   fmap :: (forall a. p a -> q a) -> g p -> g q

(<$>) :: Functor g => (forall a. p a -> q a) -> g p -> g q
(<$>) = fmap

-- | Equivalent of 'Foldable' for rank 2 data types
class Functor g => Foldable g where
   foldMap :: Monoid m => (forall a. p a -> m) -> g p -> m

-- | Equivalent of 'Traversable' for rank 2 data types
class Foldable g => Traversable g where
   traverse :: Rank1.Applicative m => (forall a. p a -> m (q a)) -> g p -> m (g q)

newtype Arrow p q a = Arrow{apply :: p a -> q a}

-- | Equivalent of 'Rank1.Applicative' with no 'pure' method, for rank 2 data types
--
-- > (.) <$> u <*> v <*> w == u <*> (v <*> w)
class Functor g => Apply g where
   ap :: g (Arrow p q) -> g p -> g q

(<*>) :: Apply g => g (Arrow p q) -> g p -> g q
(<*>) = ap

liftA2 :: Apply g => (forall a. p a -> q a -> r a) -> g p -> g q -> g r
liftA2 f g h = (Arrow . f) <$> g <*> h

liftA3 :: Apply g => (forall a. p a -> q a -> r a -> s a) -> g p -> g q -> g r -> g s
liftA3 f g h i = (\x-> Arrow (Arrow . f x)) <$> g <*> h <*> i

-- | Subclass of 'Functor' that allows access to parts of the data structure
class Functor g => Reassemblable g where
   reassemble :: (forall a. (forall f. g f -> f a) -> g p -> q a) -> g p -> g q

data Empty (f :: * -> *) = Empty deriving (Eq, Ord, Show)

newtype Singleton a (f :: * -> *) = Singleton {getSingle :: f a} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Identity' for rank 2 data types
newtype Identity g (f :: * -> *) = Identity {runIdentity :: g f} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Product' for rank 2 data types
data Product g h (f :: * -> *) = Pair {fst :: g f,
                                       snd :: h f}
                               deriving (Eq, Ord, Show)

instance Functor Empty where
   fmap _ Empty = Empty

instance Functor (Singleton a) where
   fmap f (Singleton a) = Singleton (f a)

instance Functor g => Functor (Identity g) where
   fmap f (Identity g) = Identity (fmap f g)

instance (Functor g, Functor h) => Functor (Product g h) where
   fmap f (Pair g h) = Pair (fmap f g) (fmap f h)

instance Foldable Empty where
   foldMap _ Empty = mempty

instance Foldable (Singleton x) where
   foldMap f (Singleton x) = f x

instance Foldable g => Foldable (Identity g) where
   foldMap f (Identity g) = foldMap f g

instance (Foldable g, Foldable h) => Foldable (Product g h) where
   foldMap f (Pair g h) = foldMap f g <> foldMap f h

instance Traversable Empty where
   traverse _ Empty = Rank1.pure Empty

instance Traversable (Singleton x) where
   traverse f (Singleton x) = Singleton Rank1.<$> f x

instance Traversable g => Traversable (Identity g) where
   traverse f (Identity g) = Identity Rank1.<$> traverse f g

instance (Traversable g, Traversable h) => Traversable (Product g h) where
   traverse f (Pair g h) = Pair Rank1.<$> traverse f g Rank1.<*> traverse f h

instance Apply Empty where
   ap Empty Empty = Empty

instance Apply (Singleton x) where
   ap (Singleton f) (Singleton x) = Singleton (apply f x)

instance Apply g => Apply (Identity g) where
   ap (Identity g) (Identity h) = Identity (ap g h)

instance (Apply g, Apply h) => Apply (Product g h) where
   ap (Pair gf hf) (Pair g h) = Pair (ap gf g) (ap hf h)

instance Reassemblable Empty where
   reassemble _ Empty = Empty

instance Reassemblable (Singleton x) where
   reassemble f s@Singleton{} = Singleton (f getSingle s)

instance forall g. Reassemblable g => Reassemblable (Identity g) where
   reassemble :: forall p q. (forall a. (forall f. Identity g f -> f a) -> Identity g p -> q a)
              -> Identity g p -> Identity g q
   reassemble f ~(Identity a) = Identity (reassemble f' a)
      where f' :: forall a. (forall f. g f -> f a) -> g p -> q a
            f' get x = f (get . runIdentity) (Identity x)

instance forall g h. (Reassemblable g, Reassemblable h) => Reassemblable (Product g h) where
   reassemble :: forall p q. (forall a. (forall f. Product g h f -> f a) -> Product g h p -> q a)
              -> Product g h p -> Product g h q
   reassemble f ~(Pair a b) = Pair (reassemble f' a) (reassemble f'' b)
      where f' :: forall a. (forall f. g f -> f a) -> g p -> q a
            f' get x = f (get . fst) (Pair x b)
            f'' :: forall a. (forall f. h f -> f a) -> h p -> q a
            f'' get x = f (get . snd) (Pair a x)
