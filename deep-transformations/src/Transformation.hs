{-# Language FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation where

import qualified Data.Functor as Rank1
import Data.Functor.Product (Product(Pair))
import Data.Functor.Sum (Sum(InL, InR))
import Data.Kind (Type)
import Data.Monoid (Ap)
import Data.Semigroup (Semigroup((<>)))
import qualified Rank2

import Prelude hiding (Functor(..), (<$>), fst, snd)

class Transformation t where
   type Domain t :: Type -> Type
   type Codomain t :: Type -> Type

class Transformation t => Functor t x where
   -- | Use the transformation @t@ to map 'Domain' to the 'Codomain' functor.
   (<$>) :: t -> Domain t x -> Codomain t x

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

instance (Functor t1 x, Functor t2 x, Domain t1 ~ Domain t2) => Functor (t1, t2) x where
   (t1, t2) <$> x = Pair (t1 <$> x) (t2 <$> x)

instance (Transformation t1, Transformation t2, Domain t1 ~ Domain t2) => Transformation (Either t1 t2) where
   type Domain (Either t1 t2) = Domain t1
   type Codomain (Either t1 t2) = Sum (Codomain t1) (Codomain t2)

instance (Functor t1 x, Functor t2 x, Domain t1 ~ Domain t2) => Functor (Either t1 t2) x where
   Left t <$> x = InL (t <$> x)
   Right t <$> x = InR (t <$> x)
