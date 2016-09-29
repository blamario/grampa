{-# LANGUAGE InstanceSigs, KindSignatures, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa.Classes (Functor1(..), Apply1(..), Alternative1(..), Foldable1(..), Traversable1(..),
                            Reassemblable(..), Empty1(..), Singleton1(..), Identity1(..), Product1(..), Arrow1(..))
where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (Monad(..), MonadPlus(..))
import Control.Monad.Trans.State (State, evalState, get, modify)
import Data.Function(fix)
import Data.Functor.Classes (Show1(liftShowsPrec))
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.Monoid (Monoid(mappend, mempty), All(..), (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(spanMaybe', splitPrimePrefix, tails))

-- | Equivalent of 'Functor' for rank 2 data types
class Functor1 g where
   fmap1 :: (forall a. p a -> q a) -> g p -> g q

-- | Equivalent of 'Foldable' for rank 2 data types
class Functor1 g => Foldable1 g where
   foldMap1 :: Monoid m => (forall a. p a -> m) -> g p -> m

-- | Equivalent of 'Traversable' for rank 2 data types
class Foldable1 g => Traversable1 g where
   traverse1 :: Applicative m => (forall a. p a -> m (q a)) -> g p -> m (g q)

data Arrow1 p q a = Arrow1{apply1 :: p a -> q a}

-- | Equivalent of 'Applicative' with no 'pure' method, for rank 2 data types
--
-- > (.) <$> u <*> v <*> w == u <*> (v <*> w)
class Functor1 g => Apply1 g where
   ap1 :: g (Arrow1 p q) -> g p -> g q

-- | Equivalent of 'Applicative' with no 'pure' method, for rank 2 data types
--
-- > choose1 empty1 x == x
-- > choose1 x empty1 == x
-- > x `choose1` (y `choose1` z) == (x `choose1` y) `choose1` z
-- > ap1 empty x == empty
-- > ap1 x (choose1 y z) == choose1 (ap1 x y) (ap1 x z)
-- > ap1 (choose1 x y) z == choose1 (ap1 x z) (ap1 y z)
class Apply1 g => Alternative1 g where
   empty1 :: Alternative p => g p
   choose1 :: Alternative p => g p -> g p -> g p

-- | Subclass of 'Functor' that allows access to parts of the data structure
class Functor1 g => Reassemblable g where
   reassemble :: (forall a. (forall f. g f -> f a) -> g p -> q a) -> g p -> g q

data Empty1 (f :: * -> *) = Empty1 deriving (Eq, Ord, Show)

data Singleton1 a (f :: * -> *) = Singleton1 {getSingle :: f a} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Identity' for rank 2 data types
data Identity1 g (f :: * -> *) = Identity1 {runIdentity1 :: g f} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Product' for rank 2 data types
data Product1 g h (f :: * -> *) = Pair {fst1 :: g f,
                                        snd1 :: h f}
                                deriving (Eq, Ord, Show)

instance Functor1 Empty1 where
   fmap1 f Empty1 = Empty1

instance Functor1 (Singleton1 a) where
   fmap1 f (Singleton1 a) = Singleton1 (f a)

instance Functor1 g => Functor1 (Identity1 g) where
   fmap1 f (Identity1 g) = Identity1 (fmap1 f g)

instance (Functor1 g, Functor1 h) => Functor1 (Product1 g h) where
   fmap1 f (Pair g h) = Pair (fmap1 f g) (fmap1 f h)

instance Foldable1 Empty1 where
   foldMap1 f Empty1 = mempty

instance Foldable1 (Singleton1 x) where
   foldMap1 f (Singleton1 x) = f x

instance Foldable1 g => Foldable1 (Identity1 g) where
   foldMap1 f (Identity1 g) = foldMap1 f g

instance (Foldable1 g, Foldable1 h) => Foldable1 (Product1 g h) where
   foldMap1 f (Pair g h) = foldMap1 f g <> foldMap1 f h

instance Traversable1 Empty1 where
   traverse1 f Empty1 = pure Empty1

instance Traversable1 (Singleton1 x) where
   traverse1 f (Singleton1 x) = Singleton1 <$> f x

instance Traversable1 g => Traversable1 (Identity1 g) where
   traverse1 f (Identity1 g) = Identity1 <$> traverse1 f g

instance (Traversable1 g, Traversable1 h) => Traversable1 (Product1 g h) where
   traverse1 f (Pair g h) = Pair <$> traverse1 f g <*> traverse1 f h

instance Apply1 Empty1 where
   ap1 Empty1 Empty1 = Empty1

instance Apply1 (Singleton1 x) where
   ap1 (Singleton1 f) (Singleton1 x) = Singleton1 (apply1 f x)

instance Apply1 g => Apply1 (Identity1 g) where
   ap1 (Identity1 g) (Identity1 h) = Identity1 (ap1 g h)

instance (Apply1 g, Apply1 h) => Apply1 (Product1 g h) where
   ap1 (Pair gf hf) (Pair g h) = Pair (ap1 gf g) (ap1 hf h)

instance Alternative1 Empty1 where
   empty1 = Empty1
   choose1 Empty1 Empty1 = Empty1

instance Alternative1 (Singleton1 x) where
   empty1 = Singleton1 empty
   choose1 (Singleton1 x) (Singleton1 y) = Singleton1 (x <|> y)

instance Alternative1 g => Alternative1 (Identity1 g) where
   empty1 = Identity1 empty1
   choose1 (Identity1 g) (Identity1 h) = Identity1 (choose1 g h)

instance (Alternative1 g, Alternative1 h) => Alternative1 (Product1 g h) where
   empty1 = Pair empty1 empty1
   choose1 (Pair g1 h1) (Pair g2 h2) = Pair (choose1 g1 g2) (choose1 h1 h2)

instance Reassemblable Empty1 where
   reassemble f Empty1 = Empty1

instance Reassemblable (Singleton1 x) where
   reassemble f s@(Singleton1 x) = Singleton1 (f getSingle s)

instance forall g. Reassemblable g => Reassemblable (Identity1 g) where
   reassemble :: forall p q. (forall a. (forall f. Identity1 g f -> f a) -> Identity1 g p -> q a)
              -> Identity1 g p -> Identity1 g q
   reassemble f ~(Identity1 a) = Identity1 (reassemble f' a)
      where f' :: forall a. (forall f. g f -> f a) -> g p -> q a
            f' get x = f (get . runIdentity1) (Identity1 x)

instance forall g h. (Reassemblable g, Reassemblable h) => Reassemblable (Product1 g h) where
   reassemble :: forall p q. (forall a. (forall f. Product1 g h f -> f a) -> Product1 g h p -> q a)
              -> Product1 g h p -> Product1 g h q
   reassemble f ~(Pair a b) = Pair (reassemble f' a) (reassemble f'' b)
      where f' :: forall a. (forall f. g f -> f a) -> g p -> q a
            f' get x = f (get . fst1) (Pair x b)
            f'' :: forall a. (forall f. h f -> f a) -> h p -> q a
            f'' get x = f (get . snd1) (Pair a x)
