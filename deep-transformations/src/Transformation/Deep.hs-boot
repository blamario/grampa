{-# Language KindSignatures, MultiParamTypeClasses, RankNTypes #-}

module Transformation.Deep where

import Data.Kind (Type)
import qualified Rank2
import           Transformation (Transformation, TraversableTransformation, Domain, Codomain, Algebra)

import Prelude hiding (Functor, Traversable, (<$>), traverse)

class (Transformation t, Rank2.Functor (g (Domain t))) => Functor t g where
   (<$>) :: t -> g (Domain t) (Domain t) -> g (Codomain t) (Codomain t)

class (TraversableTransformation t, Rank2.Traversable (g (Domain t))) => Traversable t g where
   traverse :: t -> g (Domain t) (Domain t) -> Algebra t (g (Codomain t) (Codomain t))
