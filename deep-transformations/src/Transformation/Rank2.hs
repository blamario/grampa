{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}

module Transformation.Rank2 where

import qualified Transformation as Shallow
import qualified Transformation.Deep as Deep

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

newtype Map p q = Map (forall x. p x -> q x)

newtype Fold p m = Fold (forall x. p x -> m)

newtype Traversal p q m = Traversal (forall x. p x -> m (q x))

instance Shallow.Functor (Map p q) p q x where
   (<$>) (Map f) = f

instance Shallow.Foldable (Fold p m) p m x where
   foldMap (Fold f) = f

instance Shallow.Traversable (Traversal p q m) p q m x where
   traverse (Traversal t) = t

(<$>) :: Deep.Functor (Map p q) g p q => (forall a. p a -> q a) -> g p p -> g q q
(<$>) f = (Deep.<$>) (Map f)

foldMap :: (Deep.Foldable (Fold p m) g p m, Monoid m) => (forall a. p a -> m) -> g p p -> m
foldMap f = Deep.foldMap (Fold f)

traverseDown :: Deep.DownTraversable (Traversal p q m) g p q m => (forall a. p a -> m (q a)) -> g p p -> m (g q q)
traverseDown f = Deep.traverseDown (Traversal f)

traverseUp :: Deep.UpTraversable (Traversal p q m) g p q m => (forall a. p a -> m (q a)) -> g p p -> m (g q q)
traverseUp f = Deep.traverseUp (Traversal f)
