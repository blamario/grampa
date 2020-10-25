{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, TypeFamilies, UndecidableInstances #-}

-- | This module provides natural transformations 'Map', 'Fold', and 'Traversal', as well as three rank-2 functions
-- that wrap them in a convenient interface.

module Transformation.Rank2 where

import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.Functor.Const (Const(Const, getConst))
import qualified Rank2
import           Transformation (Transformation, Domain, Codomain)
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

-- | Transform (naturally) the containing functor of every node in the given tree.
(<$>) :: Deep.Functor (Map p q) g => (forall a. p a -> q a) -> g p p -> g q q
(<$>) f = (Deep.<$>) (Map f)

-- | Fold the containing functor of every node in the given tree.
foldMap :: (Deep.Functor (Fold p m) g, Rank2.Foldable (g (Const m)), Monoid m) => (forall a. p a -> m) -> g p p -> m
foldMap f = Rank2.foldMap getConst . Deep.fmap (Fold f)

-- | Traverse the containing functors of all nodes in the given tree.
traverse :: Deep.Traversable (Traversal p q m) g => (forall a. p a -> m (q a)) -> g p p -> m (g q q)
traverse f = Deep.traverse (Traversal f)

newtype Map p q = Map (forall x. p x -> q x)

newtype Fold p m = Fold (forall x. p x -> m)

newtype Traversal p q m = Traversal (forall x. p x -> m (q x))

instance Transformation (Map p q) where
   type Domain (Map p q) = p
   type Codomain (Map p q) = q

instance Transformation (Fold p m) where
   type Domain (Fold p m) = p
   type Codomain (Fold p m) = Const m

instance Transformation (Traversal p q m) where
   type Domain (Traversal p q m) = p
   type Codomain (Traversal p q m) = Compose m q

instance Transformation.At (Map p q) x where
   ($) (Map f) = f

instance Transformation.At (Fold p m) x where
   ($) (Fold f) = Const . f

instance Transformation.At (Traversal p q m) x where
   ($) (Traversal f) = Compose . f

instance (Deep.Functor (Map p q) g, Functor p) => Full.Functor (Map p q) g where
  (<$>) = Full.mapUpDefault
