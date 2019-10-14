{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, TypeFamilies, UndecidableInstances #-}

module Transformation.Rank2 where

import Data.Functor.Const (Const)
import Data.Void (Void)
import           Transformation (Transformation, Domain, Codomain)
import qualified Transformation as Shallow
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

newtype Map p q = Map (forall x. p x -> q x)

newtype Fold p m = Fold (forall x. p x -> m)

newtype Traversal p q m = Traversal (forall x. p x -> m (q x))

instance Transformation (Map p q) where
   type Domain (Map p q) = p
   type Codomain (Map p q) = q

instance Transformation (Fold p m) where
   type Domain (Fold p m) = p
   type Codomain (Fold p m) = Const Void

instance Transformation (Traversal p q m) where
   type Domain (Traversal p q m) = p
   type Codomain (Traversal p q m) = q

instance Shallow.Functor (Map p q) x where
   (<$>) (Map f) = f

instance Shallow.Foldable (Fold p m) m x where
   foldMap (Fold f) = f

instance Shallow.Traversable (Traversal p q m) m x where
   traverse (Traversal t) = t

(<$>) :: Deep.Functor (Map p q) g => (forall a. p a -> q a) -> g p p -> g q q
(<$>) f = (Deep.<$>) (Map f)

foldMap :: (Deep.Foldable (Fold p m) g m, Monoid m) => (forall a. p a -> m) -> g p p -> m
foldMap f = Deep.foldMap (Fold f)

traverse :: Deep.Traversable (Traversal p q m) g m => (forall a. p a -> m (q a)) -> g p p -> m (g q q)
traverse f = Deep.traverse (Traversal f)

instance (Deep.Functor (Map p q) g, Functor p) => Full.Functor (Map p q) g where
  (<$>) = Full.mapUpDefault

instance (Deep.Foldable (Fold p m) g m, Monoid m, Foldable p) => Full.Foldable (Fold p m) g m where
  foldMap = Full.foldMapDefault

instance (Deep.Traversable (Traversal p q m) g m, Monad m, Traversable p) =>
         Full.Traversable (Traversal p q m) g m where
  traverse = Full.traverseUpDefault
