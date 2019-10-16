{-# Language FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation where

import Control.Applicative (Applicative, liftA2)
import qualified Data.Functor as Rank1
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.Functor.Product (Product(Pair))
import Data.Functor.Sum (Sum(InL, InR))
import Data.Kind (Type)
import Data.Monoid (Ap)
import Data.Semigroup (Semigroup((<>)))
import qualified Rank2

import Prelude hiding (Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Transformation t where
   type Domain t :: Type -> Type
   type Codomain t :: Type -> Type

class Transformation t => TraversableTransformation t where
   type Algebra t :: Type -> Type

class Transformation t => Functor t x where
   -- | Use the transformation @t@ to map 'Domain' to the 'Codomain' functor.
   (<$>) :: t -> Domain t x -> Codomain t x

class TraversableTransformation t => Traversable t x where
   traverse :: t -> Domain t x -> Algebra t (Codomain t x)

-- | Traditional synonym for '<$>'
fmap :: Functor t x => t -> Domain t x -> Codomain t x
fmap = (<$>)

data ArrowPair a b = ArrowPair a b

instance Transformation (Rank2.Arrow p q x) where
   type Domain (Rank2.Arrow p q x) = p
   type Codomain (Rank2.Arrow p q x) = q

instance Functor (Rank2.Arrow p q x) x where
   (<$>) = Rank2.apply

instance (Transformation t1, Transformation t2, Domain t1 ~ Domain t2) => Transformation (t1, t2) where
   type Domain (t1, t2) = Domain t1
   type Codomain (t1, t2) = Product (Codomain t1) (Codomain t2)

instance (TraversableTransformation t1, TraversableTransformation t2, Domain t1 ~ Domain t2) =>
         TraversableTransformation (t1, t2) where
   type Algebra (t1, t2) = Algebra t1

instance (Functor t1 x, Functor t2 x, Domain t1 ~ Domain t2) => Functor (t1, t2) x where
   (t1, t2) <$> x = Pair (t1 <$> x) (t2 <$> x)

instance (Transformation t1, Transformation t2, Domain t1 ~ Domain t2) => Transformation (Either t1 t2) where
   type Domain (Either t1 t2) = Domain t1
   type Codomain (Either t1 t2) = Sum (Codomain t1) (Codomain t2)

instance (Functor t1 x, Functor t2 x, Domain t1 ~ Domain t2) => Functor (Either t1 t2) x where
   Left t <$> x = InL (t <$> x)
   Right t <$> x = InR (t <$> x)

instance (Traversable t1 x, Traversable t2 x, Domain t1 ~ Domain t2,
          Algebra t1 ~ Algebra t2, Applicative (Algebra t1)) =>
         Traversable (t1, t2) x where
   traverse (t1, t2) x = liftA2 Pair (traverse t1 x) (traverse t2 x)
