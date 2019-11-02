{-# Language DeriveDataTypeable, FlexibleInstances, KindSignatures, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, UndecidableInstances #-}

module Transformation.Shallow where

import Control.Applicative (Applicative, (<*>), liftA2)
import Data.Data (Data, Typeable)
import Data.Kind (Type)
import qualified Rank2
import qualified Data.Functor
import           Transformation (Transformation, TraversableTransformation, Domain, Codomain, Algebra)

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Transformation t => Functor t g where
   (<$>) :: t -> g (Domain t) -> g (Codomain t)

class TraversableTransformation t => Traversable t g where
   traverse :: t -> g (Domain t) -> Algebra t (g (Codomain t))

instance (Functor t g, Functor t h) => Functor t (Rank2.Product g h) where
   t <$> Rank2.Pair left right = Rank2.Pair (t <$> left) (t <$> right)

instance (Traversable t g, Traversable t h, Applicative (Algebra t)) => Traversable t (Rank2.Product g h) where
   traverse t (Rank2.Pair left right) = liftA2 Rank2.Pair (traverse t left) (traverse t right)

fmap :: Functor t g => t -> g (Domain t) -> g (Codomain t)
fmap = (<$>)
