{-# Language KindSignatures, MultiParamTypeClasses, RankNTypes, TypeFamilies #-}

module Transformation.Deep where

import Data.Functor.Compose (Compose)
import Data.Functor.Const (Const)
import Data.Kind (Type)
import qualified Rank2
import           Transformation (Transformation, Domain, Codomain)

import Prelude hiding (Functor, Foldable, Traversable, (<$>), foldMap, traverse)

class (Transformation t, Rank2.Functor (g (Domain t))) => Functor t g where
   (<$>) :: t -> g (Domain t) (Domain t) -> g (Codomain t) (Codomain t)

class (Transformation t, Rank2.Foldable (g (Domain t))) => Foldable t g where
   foldMap :: (Codomain t ~ Const m, Monoid m) => t -> g (Domain t) (Domain t) -> m

class (Transformation t, Rank2.Traversable (g (Domain t))) => Traversable t g where
   traverse :: Codomain t ~ Compose m f => t -> g (Domain t) (Domain t) -> m (g f f)
