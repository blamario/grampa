{-# Language KindSignatures, MultiParamTypeClasses, RankNTypes #-}

module Transformation.Deep where

import qualified Rank2

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>))

class Rank2.Functor (g p) => Functor t g (p :: * -> *) (q :: * -> *) where
   (<$>) :: t -> g p p -> g q q

class Rank2.Foldable (g p) => Foldable t g p m where
   foldMap :: t -> g p p -> m

class Rank2.Traversable (g p) => Traversable t g (p :: * -> *) (q :: * -> *) m where
   traverse :: t -> g p p -> m (g q q)
