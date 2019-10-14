{-# Language KindSignatures, MultiParamTypeClasses, RankNTypes #-}

module Transformation.Deep where

import qualified Rank2
import           Transformation (Transformation, Domain, Codomain)

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>))

class (Transformation t, Rank2.Functor (g (Domain t))) => Functor t g where
   (<$>) :: t -> g (Domain t) (Domain t) -> g (Codomain t) (Codomain t)

class (Transformation t, Rank2.Foldable (g (Domain t))) => Foldable t g m where
   foldMap :: t -> g (Domain t) (Domain t) -> m

class (Transformation t, Rank2.Traversable (g (Domain t))) => Traversable t g m where
   traverse :: t -> g (Domain t) (Domain t) -> m (g (Codomain t) (Codomain t))
