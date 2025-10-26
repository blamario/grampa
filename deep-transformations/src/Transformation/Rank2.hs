{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, TypeFamilies, UndecidableInstances #-}

-- | This module provides natural transformations 'Map', 'Fold', and 'Traversal', as well as three rank-2 functions
-- that wrap them in a convenient interface.

module Transformation.Rank2 where

import Data.Functor.Compose (Compose(Compose))
import Data.Functor.Const (Const(Const))
import Data.Kind (Type)
import           Transformation (Transformation, Domain, Codomain)
import qualified Transformation
import qualified Transformation.Deep as Deep

-- | Transform (naturally) the containing functor of every node in the given tree.
(<$>) :: Deep.Functor (Map p q) g => (forall a. p a -> q a) -> g p p -> g q q
f <$> x = Map f Deep.<$> x
infixl 4 <$>

-- | Fold the containing functor of every node in the given tree.
foldMap :: (Deep.Foldable (Fold p m) g, Monoid m) => (forall a. p a -> m) -> g p p -> m
foldMap f = Deep.foldMap (Fold f)

-- | Traverse the containing functors of all nodes in the given tree.
traverse :: Deep.Traversable (Traversal p q m) g => (forall a. p a -> m (q a)) -> g p p -> m (g q q)
traverse f = Deep.traverse (Traversal f)

newtype Map (p :: Type -> Type) (q :: Type -> Type) = Map (forall x. p x -> q x)

newtype Fold (p :: Type -> Type) m = Fold (forall x. p x -> m)

newtype Traversal (p :: Type -> Type) (q :: Type -> Type) m = Traversal (forall x. p x -> m (q x))

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
