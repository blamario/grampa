{-# Language DataKinds, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | A /natural transformation/ is a concept from category theory for a mapping between two functors and their objects
-- that preserves a naturality condition. In Haskell the naturality condition boils down to parametricity, so a
-- natural transformation between two functors @f@ and @g@ is represented as
--
-- > type NaturalTransformation f g = ∀a. f a → g a
--
-- This type appears in several Haskell libraries, most obviously in
-- [natural-transformations](https://hackage.haskell.org/package/natural-transformation). There are times, however,
-- when we crave more control. Sometimes what we want to do depends on which type @a@ is hiding in that @f a@ we're
-- given. Sometimes, in other words, we need an /unnatural/ transformation.
--
-- This means we have to abandon parametricity for ad-hoc polymorphism, and that means type classes. There are two
-- steps to defining a transformation:
--
-- * an instance of the base class 'Transformation' declares the two functors being mapped, much like a function type
--   signature,
-- * while the actual mapping of values is performed by an arbitrary number of instances of the method '$', a bit like
--   multiple equation clauses that make up a single function definition.
--
-- The module is meant to be imported qualified.

module Transformation where

import Data.Coerce (coerce)
import qualified Data.Functor.Compose as Functor
import Data.Functor.Const (Const)
import Data.Functor.Product (Product(Pair))
import Data.Functor.Sum (Sum(InL, InR))
import Data.Kind (Type)
import GHC.TypeLits (ErrorMessage (Text, ShowType, (:<>:)), TypeError)
import qualified Rank2

import Prelude hiding (($))

-- | A 'Transformation', natural or not, maps one functor to another.
class Transformation t where
   type Domain t :: Type -> Type
   type Codomain t :: Type -> Type

-- | An unnatural 'Transformation' can behave differently at different points.
class Transformation t => At t x where
   -- | Apply the transformation @t@ at type @x@ to map 'Domain' to the 'Codomain' functor.
   ($) :: t -> Domain t x -> Codomain t x
   infixr 0 $

-- | Alphabetical synonym for '$'
apply :: t `At` x => t -> Domain t x -> Codomain t x
apply = ($)

-- | Composition of two transformations
data Compose t u = Compose t u

-- | Transformation under a 'Data.Functor.Functor'
newtype Mapped (f :: Type -> Type) t = Mapped t

-- | Transformation under a 'Foldable'
newtype Folded (f :: Type -> Type) t = Folded t

-- | Transformation under a 'Traversable'
newtype Traversed (f :: Type -> Type) t = Traversed t

instance (Transformation t, Transformation u, Domain t ~ Codomain u) => Transformation (Compose t u) where
   type Domain (Compose t u) = Domain u
   type Codomain (Compose t u) = Codomain t

instance Transformation t => Transformation (Mapped f t) where
   type Domain (Mapped f t) = Functor.Compose f (Domain t)
   type Codomain (Mapped f t) = Functor.Compose f (Codomain t)

instance Transformation t => Transformation (Folded f t) where
   type Domain (Folded f t) = Functor.Compose f (Domain t)
   type Codomain (Folded f t) = Codomain t

instance (Transformation t, Codomain t ~ Functor.Compose m n) => Transformation (Traversed f t) where
   type Domain (Traversed f t) = Functor.Compose f (Domain t)
   type Codomain (Traversed f t) =
      Functor.Compose (ComposeOuter (Codomain t)) (Functor.Compose f (ComposeInner (Codomain t)))

type family ComposeOuter (c :: Type -> Type) :: Type -> Type where
   ComposeOuter (Functor.Compose p q) = p

type family ComposeInner (c :: Type -> Type) :: Type -> Type where
   ComposeInner (Functor.Compose p q) = q

instance (t `At` x, u `At` x, Domain t ~ Codomain u) => Compose t u `At` x where
   Compose t u $ x =  t $ u $ x

instance (t `At` x, Functor f) => Mapped f t `At` x where
   Mapped t $ Functor.Compose x = Functor.Compose ((t $) <$> x)

instance (t `At` x, Foldable f, Codomain t ~ Const m, Monoid m) => Folded f t `At` x where
   Folded t $ Functor.Compose x = foldMap (t $) x

instance (t `At` x, Traversable f, Codomain t ~ Functor.Compose m n, Applicative m) => Traversed f t `At` x where
   Traversed t $ Functor.Compose x = Functor.Compose (Functor.Compose <$> traverse (Functor.getCompose . (t $)) x)

instance Transformation (Rank2.Arrow (p :: Type -> Type) q x) where
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
