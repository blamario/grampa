{-# Language KindSignatures, MultiParamTypeClasses, RankNTypes, TypeFamilies #-}

module Transformation.Deep where

import Data.Functor.Compose (Compose)
import Data.Kind (Type)
import qualified Rank2
import           Transformation (Transformation, Domain, Codomain)

import Prelude hiding (Functor, Traversable, (<$>), traverse)

class (Transformation t, Rank2.Functor (g (Domain t))) => Functor t g where
   (<$>) :: t -> g (Domain t) (Domain t) -> g (Codomain t) (Codomain t)

class (Transformation t, Rank2.Traversable (g (Domain t))) => Traversable t g where
   traverse :: Codomain t ~ Compose m f => t -> g (Domain t) (Domain t) -> m (g f f)
