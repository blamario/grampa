{-# Language DeriveDataTypeable, FlexibleInstances, KindSignatures, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, TypeFamilies, UndecidableInstances #-}

module Transformation.Shallow where

import Control.Applicative (Applicative, (<*>), liftA2)
import Data.Data (Data, Typeable)
import Data.Functor.Compose (Compose)
import Data.Kind (Type)
import qualified Rank2
import qualified Data.Functor
import           Transformation (Transformation, Domain, Codomain)

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Transformation t => Functor t g where
   (<$>) :: t -> g (Domain t) -> g (Codomain t)

class Transformation t => Traversable t g where
   traverse :: Codomain t ~ Compose m f => t -> g (Domain t) -> m (g f)

instance (Functor t g, Functor t h) => Functor t (Rank2.Product g h) where
   t <$> Rank2.Pair left right = Rank2.Pair (t <$> left) (t <$> right)

instance (Traversable t g, Traversable t h, Codomain t ~ Compose m f, Applicative m) => Traversable t (Rank2.Product g h) where
   traverse t (Rank2.Pair left right) = liftA2 Rank2.Pair (traverse t left) (traverse t right)

fmap :: Functor t g => t -> g (Domain t) -> g (Codomain t)
fmap = (<$>)
