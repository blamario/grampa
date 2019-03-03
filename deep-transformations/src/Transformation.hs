{-# Language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             ScopedTypeVariables, TypeOperators, UndecidableInstances #-}

module Transformation where

import Control.Applicative (Applicative, liftA2)
import qualified Data.Functor as Rank1
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.Functor.Product (Product(Pair))
import Data.Functor.Sum (Sum(InL, InR))
import Data.Semigroup (Semigroup((<>)))
import qualified Rank2

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Functor t p q x | t -> p q where
   -- | Use the transformation @t@ to map functor @p@ to functor @q@.
   (<$>) :: t -> p x -> q x

class Foldable t p m x | t -> p m where
   foldMap :: t -> p x -> m

class Traversable t p q m x | t -> p q m where
   traverse :: t -> p x -> m (q x)

-- | Traditional synonym for '<$>'
fmap :: Functor t p q x => t -> p x -> q x
fmap = (<$>)

data ArrowPair a b = ArrowPair a b

instance Functor (Rank2.Arrow p q x) p q x where
   (<$>) = Rank2.apply

instance (Functor t1 p q x, Functor t2 p r x) => Functor (t1, t2) p (Product q r) x where
   (t1, t2) <$> x = Pair (t1 <$> x) (t2 <$> x)

instance (Functor t1 p q x, Functor t2 p r x) => Functor (Either t1 t2) p (Sum q r) x where
   Left t <$> x = InL (t <$> x)
   Right t <$> x = InR (t <$> x)

instance (Functor t1 p (q1 Rank2.~> r1) x, Functor t2 p (q2 Rank2.~> r2) x) =>
         Functor (ArrowPair t1 t2) p (Product q1 q2 Rank2.~> Product r1 r2) x where
   ArrowPair t1 t2 <$> x = Rank2.Arrow flatten <$> ((t1, t2) <$> x)
      where flatten :: Product (Rank2.Arrow q1 r1) (Rank2.Arrow q2 r2) x -> Rank2.Arrow (Product q1 q2) (Product r1 r2) x
            flatten (Pair (Rank2.Arrow f1) (Rank2.Arrow f2)) = Rank2.Arrow (\(Pair x1 x2) -> Pair (f1 x1) (f2 x2))

instance (Foldable t1 p m x, Foldable t2 p m x, Semigroup m) => Foldable (t1, t2) p m x where
   foldMap (t1, t2) x = foldMap t1 x <> foldMap t2 x

instance (Foldable t1 p m x, Foldable t2 p m x) => Foldable (Either t1 t2) p m x where
   foldMap (Left t) x = foldMap t x
   foldMap (Right t) x = foldMap t x

instance (Traversable t1 p q m x, Traversable t2 p r m x, Applicative m) => Traversable (t1, t2) p (Product q r) m x where
   traverse (t1, t2) x = liftA2 Pair (traverse t1 x) (traverse t2 x)
