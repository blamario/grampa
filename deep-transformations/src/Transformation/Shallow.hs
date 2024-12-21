{-# Language DeriveDataTypeable, FlexibleInstances, KindSignatures, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | Type classes 'Functor', 'Foldable', and 'Traversable' that correspond to the standard type classes of the same
-- name. The [rank2classes](https://hackage.haskell.org/package/rank2classes) package provides the equivalent set
-- of classes for natural transformations. This module extends the functionality to unnatural transformations.

module Transformation.Shallow where

import Control.Applicative (Applicative, liftA2, pure)
import qualified Data.Functor as Rank1
import Data.Functor.Compose (Compose(getCompose))
import Data.Functor.Const (Const(Const, getConst))
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

instance Transformation t => Foldable t Rank2.Empty where
   foldMap _ _ = mempty

instance Transformation t => Foldable t Proxy where
   foldMap _ _ = mempty

instance Transformation t => Foldable t (Const x) where
   foldMap _ _ = mempty

instance (Transformation t, t `At` a, Codomain t ~ Const m) => Foldable t (Rank2.Only a) where
   foldMap t (Rank2.Only x) = getConst (t Transformation.$ x)

instance Foldable t g => Foldable t (Rank2.Identity g) where
   foldMap f (Rank2.Identity g) = foldMap f g

instance (Transformation t, Codomain t ~ Compose m f, Applicative m) => Traversable t Rank2.Empty where
   traverse _ _ = pure Rank2.Empty

instance (Transformation t, Codomain t ~ Compose m f, Applicative m) => Traversable t Proxy where
   traverse _ _ = pure Proxy

instance (Transformation t, Codomain t ~ Compose m f, Applicative m) => Traversable t (Const x) where
   traverse _ (Const x) = pure (Const x)

instance (Transformation t, t `At` a, Codomain t ~ Compose m f, Rank1.Functor m) => Traversable t (Rank2.Only a) where
   traverse t (Rank2.Only x) = Rank2.Only Rank1.<$> getCompose (t Transformation.$ x)

instance (Traversable t g, Codomain t ~ Compose m f, Rank1.Functor m) => Traversable t (Rank2.Identity g) where
   traverse f (Rank2.Identity g) = Rank2.Identity Rank1.<$> traverse f g

instance (Functor t g, Functor t h) => Functor t (Rank2.Product g h) where
   t <$> Rank2.Pair left right = Rank2.Pair (t <$> left) (t <$> right)

instance (Foldable t g, Foldable t h, Codomain t ~ Const m, Monoid m) => Foldable t (Rank2.Product g h) where
   foldMap t (Rank2.Pair left right) = foldMap t left `mappend` foldMap t right

instance (Traversable t g, Traversable t h, Codomain t ~ Compose m f, Applicative m) => Traversable t (Rank2.Product g h) where
   traverse t (Rank2.Pair left right) = liftA2 Rank2.Pair (traverse t left) (traverse t right)

-- | Alphabetical synonym for '<$>'
fmap :: Functor t g => t -> g (Domain t) -> g (Codomain t)
fmap = (<$>)
