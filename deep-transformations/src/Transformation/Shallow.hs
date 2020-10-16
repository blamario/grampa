{-# Language DeriveDataTypeable, FlexibleInstances, KindSignatures, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, TypeFamilies, UndecidableInstances #-}

-- | Type classes 'Functor', 'Foldable', and 'Traversable' that correspond to the standard type classes of the same
-- name. The [rank2classes](https://hackage.haskell.org/package/rank2classes) package provides the equivalent set
-- of classes for natural transformations.

module Transformation.Shallow where

import Control.Applicative (Applicative, (<*>), liftA2)
import Data.Data (Data, Typeable)
import Data.Functor.Compose (Compose)
import Data.Functor.Const (Const)
import Data.Kind (Type)
import qualified Rank2
import qualified Data.Functor
import           Transformation (Transformation, Domain, Codomain)

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

-- | Like 'Rank2.Functor' except it takes a 'Transformation' instead of a polymorphic function
class (Transformation t, Rank2.Functor g) => Functor t g where
   (<$>) :: t -> g (Domain t) -> g (Codomain t)

-- | Like 'Rank2.Foldable' except it takes a 'Transformation' instead of a polymorphic function
class (Transformation t, Rank2.Foldable g) => Foldable t g where
   foldMap :: (Codomain t ~ Const m, Monoid m) => t -> g (Domain t) -> m

-- | Like 'Rank2.Traversable' except it takes a 'Transformation' instead of a polymorphic function
class (Transformation t, Rank2.Traversable g) => Traversable t g where
   traverse :: Codomain t ~ Compose m f => t -> g (Domain t) -> m (g f)

instance (Functor t g, Functor t h) => Functor t (Rank2.Product g h) where
   t <$> Rank2.Pair left right = Rank2.Pair (t <$> left) (t <$> right)

instance (Foldable t g, Foldable t h, Codomain t ~ Const m, Monoid m) => Foldable t (Rank2.Product g h) where
   foldMap t (Rank2.Pair left right) = foldMap t left <> foldMap t right

instance (Traversable t g, Traversable t h, Codomain t ~ Compose m f, Applicative m) => Traversable t (Rank2.Product g h) where
   traverse t (Rank2.Pair left right) = liftA2 Rank2.Pair (traverse t left) (traverse t right)

-- | Alphabetical synonym for '<$>'
fmap :: Functor t g => t -> g (Domain t) -> g (Codomain t)
fmap = (<$>)
