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

import Prelude hiding (($))

class Transformation t where
   type Domain t :: Type -> Type
   type Codomain t :: Type -> Type

class Transformation t => At t x where
   -- | Use the transformation @t@ at type @x@ to map 'Domain' to the 'Codomain' functor.
   ($) :: t -> Domain t x -> Codomain t x
   infixr 0  $

apply :: t `At` x => t -> Domain t x -> Codomain t x
apply = ($)

data Compose t u = Compose t u

instance (Transformation t, Transformation u, Domain t ~ Codomain u) => Transformation (Compose t u) where
   type Domain (Compose t u) = Domain u
   type Codomain (Compose t u) = Codomain t

instance (t `At` x, u `At` x, Domain t ~ Codomain u) => Compose t u `At` x where
   Compose t u $ x =  t $ (u $ x)

instance Transformation (Rank2.Arrow p q x) where
   type Domain (Rank2.Arrow p q x) = p
   type Codomain (Rank2.Arrow p q x) = q

instance Rank2.Arrow p q x `At` x where
   ($) = Rank2.apply

instance (Transformation t1, Transformation t2, Domain t1 ~ Domain t2) => Transformation (t1, t2) where
   type Domain (t1, t2) = Domain t1
   type Codomain (t1, t2) = Product (Codomain t1) (Codomain t2)

instance (t `At` x, u `At` x, Domain t ~ Domain u) => (t, u) `At` x where
   (t, u) $ x = Pair (t $ x) (u $ x)

instance (Transformation t1, Transformation t2, Domain t1 ~ Domain t2) => Transformation (Either t1 t2) where
   type Domain (Either t1 t2) = Domain t1
   type Codomain (Either t1 t2) = Sum (Codomain t1) (Codomain t2)

instance (t `At` x, u `At` x, Domain t ~ Domain u) => Either t u `At` x where
   Left t $ x = InL (t $ x)
   Right t $ x = InR (t $ x)
