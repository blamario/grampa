{-# Language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}

module Transformation where

import qualified Rank2

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Functor t p q x | t -> p q where
   (<$>) :: t -> p x -> q x

class Foldable t p m x | t -> p m where
   foldMap :: t -> p x -> m

class Traversable t p q m x | t -> p q m where
   traverse :: t -> p x -> m (q x)

fmap :: Functor t p q x => t -> p x -> q x
fmap = (<$>)

instance Functor (Rank2.Arrow p q x) p q x where
   (<$>) = Rank2.apply
