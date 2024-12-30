{-# Language DeriveDataTypeable, FlexibleContexts, FlexibleInstances, KindSignatures, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | Type classes 'Functor', 'Foldable', and 'Traversable' that correspond to the standard type classes of the same
-- name. The [rank2classes](https://hackage.haskell.org/package/rank2classes) package provides the equivalent set
-- of classes for natural transformations. This module extends the functionality to unnatural transformations.

module Transformation.Shallow (Functor(..), Foldable(..), Traversable(..), fmap) where

import Control.Applicative (Applicative, liftA2, pure)
import qualified Data.Functor as Rank1 (Functor, (<$>))
import qualified Data.Foldable as Rank1 (Foldable, foldMap)
import qualified Data.Traversable as Rank1 (Traversable, traverse)
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.Functor.Const (Const(Const, getConst))
import Data.Kind (Type)
import Data.Proxy (Proxy(Proxy))
import qualified Rank2
import           Transformation (Transformation, Domain, Codomain, At)
import qualified Transformation

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

-- | Like Rank2.'Rank2.Functor' except it takes a 'Transformation' instead of a polymorphic function
class (Transformation t, Rank2.Functor g) => Functor t g where
   (<$>) :: t -> g (Domain t) -> g (Codomain t)
   infixl 4 <$>

-- | Like Rank2.'Rank2.Foldable' except it takes a 'Transformation' instead of a polymorphic function
class (Transformation t, Rank2.Foldable g) => Foldable t g where
   foldMap :: (Codomain t ~ Const m, Monoid m) => t -> g (Domain t) -> m

-- | Like Rank2.'Rank2.Traversable' except it takes a 'Transformation' instead of a polymorphic function
class (Transformation t, Rank2.Traversable g) => Traversable t g where
   traverse :: Codomain t ~ Compose m f => t -> g (Domain t) -> m (g f)

newtype FunctorCompose (p :: Type -> Type) t = FunctorCompose t
newtype FoldableCompose (p :: Type -> Type) t = FoldableCompose t
newtype TraversableCompose (p :: Type -> Type) t = TraversableCompose t

instance Transformation t => Transformation (FunctorCompose p t) where
   type Domain (FunctorCompose p t) = Compose p (Domain t)
   type Codomain (FunctorCompose p t) = Compose p (Codomain t)
instance Transformation t => Transformation (FoldableCompose p t) where
   type Domain (FoldableCompose p t) = Compose p (Domain t)
   type Codomain (FoldableCompose p t) = Codomain t
instance (Transformation t, Codomain t ~ Compose q r) => Transformation (TraversableCompose p t) where
   type Domain (TraversableCompose p t) = Compose p (Domain t)
   type Codomain (TraversableCompose p t) = Compose (Outer (Codomain t)) (Compose p (Inner (Codomain t)))

type family Outer f where
   Outer (Compose p q) = p
type family Inner f where
   Inner (Compose p q) = q

instance (Rank1.Functor p, t `At` a) => FunctorCompose p t `At` a where
   FunctorCompose t $ Compose x = Compose ((t Transformation.$) Rank1.<$> x)
instance (Rank1.Foldable p, Codomain t ~ Const m, Monoid m, t `At` a) => FoldableCompose p t `At` a where
   FoldableCompose t $ Compose x = Const $ Rank1.foldMap (getConst . (t Transformation.$)) x
instance (Rank1.Traversable p, Applicative q, Codomain t ~ Compose q r, t `At` a) => TraversableCompose p t `At` a where
   TraversableCompose t $ Compose x = Compose $ Compose Rank1.<$> Rank1.traverse (getCompose . (t Transformation.$)) x

instance Transformation t => Functor t Rank2.Empty where
   _ <$> Rank2.Empty = Rank2.Empty

instance Transformation t => Functor t Proxy where
   _ <$> _ = Proxy

instance Transformation t => Functor t (Const a) where
   _ <$> Const a = Const a

instance (Transformation t, t `At` a) => Functor t (Rank2.Only a) where
   t <$> Rank2.Only x = Rank2.Only (t Transformation.$ x)

instance Functor t g => Functor t (Rank2.Identity g) where
   f <$> Rank2.Identity g = Rank2.Identity (f <$> g)

instance (Transformation t, Functor (FunctorCompose p t) g, Rank1.Functor p) => Functor t (Rank2.Compose g p) where
   t <$> Rank2.Compose g = Rank2.Compose (FunctorCompose t <$> g)

instance (Transformation t, t `At` a, Rank1.Functor g) => Functor t (Rank2.Flip g a) where
   t <$> Rank2.Flip g = Rank2.Flip ((t Transformation.$) Rank1.<$> g)

instance Transformation t => Foldable t Rank2.Empty where
   foldMap _ _ = mempty

instance Transformation t => Foldable t Proxy where
   foldMap _ _ = mempty

instance Transformation t => Foldable t (Const x) where
   foldMap _ _ = mempty

instance (Transformation t, t `At` a, Codomain t ~ Const m) => Foldable t (Rank2.Only a) where
   foldMap t (Rank2.Only x) = getConst (t Transformation.$ x)

instance Foldable t g => Foldable t (Rank2.Identity g) where
   foldMap t (Rank2.Identity g) = foldMap t g

instance (Transformation t, Foldable (FoldableCompose p t) g, Rank1.Foldable p) => Foldable t (Rank2.Compose g p) where
   foldMap t (Rank2.Compose g) = foldMap (FoldableCompose t) g

instance (Transformation t, t `At` a, Codomain t ~ Const m, Rank1.Foldable g) => Foldable t (Rank2.Flip g a) where
   foldMap t (Rank2.Flip g) = Rank1.foldMap (getConst . (t Transformation.$)) g

instance (Transformation t, Codomain t ~ Compose m f, Applicative m) => Traversable t Rank2.Empty where
   traverse _ _ = pure Rank2.Empty

instance (Transformation t, Codomain t ~ Compose m f, Applicative m) => Traversable t Proxy where
   traverse _ _ = pure Proxy

instance (Transformation t, Codomain t ~ Compose m f, Applicative m) => Traversable t (Const x) where
   traverse _ (Const x) = pure (Const x)

instance (Transformation t, t `At` a, Codomain t ~ Compose m f, Rank1.Functor m) => Traversable t (Rank2.Only a) where
   traverse t (Rank2.Only x) = Rank2.Only Rank1.<$> getCompose (t Transformation.$ x)

instance (Traversable t g, Codomain t ~ Compose m f, Rank1.Functor m) => Traversable t (Rank2.Identity g) where
   traverse t (Rank2.Identity g) = Rank2.Identity Rank1.<$> traverse t g

instance (Transformation t, Traversable (TraversableCompose p t) g,
          Rank1.Traversable p, Codomain t ~ Compose q r, Rank1.Functor q) => Traversable t (Rank2.Compose g p) where
   traverse t (Rank2.Compose g) = Rank2.Compose Rank1.<$> traverse (TraversableCompose t) g

instance (Transformation t, t `At` a,
          Codomain t ~ Compose m f, Applicative m, Rank1.Traversable g) => Traversable t (Rank2.Flip g a) where
   traverse t (Rank2.Flip g) = Rank2.Flip Rank1.<$> Rank1.traverse (getCompose . (t Transformation.$)) g

instance (Functor t g, Functor t h) => Functor t (Rank2.Product g h) where
   t <$> Rank2.Pair left right = Rank2.Pair (t <$> left) (t <$> right)

instance (Foldable t g, Foldable t h, Codomain t ~ Const m, Monoid m) => Foldable t (Rank2.Product g h) where
   foldMap t (Rank2.Pair left right) = foldMap t left `mappend` foldMap t right

instance (Traversable t g, Traversable t h, Codomain t ~ Compose m f, Applicative m) => Traversable t (Rank2.Product g h) where
   traverse t (Rank2.Pair left right) = liftA2 Rank2.Pair (traverse t left) (traverse t right)

-- | Alphabetical synonym for '<$>'
fmap :: Functor t g => t -> g (Domain t) -> g (Codomain t)
fmap = (<$>)
