{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# Language QuantifiedConstraints, RankNTypes, TypeFamilies, TypeOperators #-}
{-# Language UndecidableInstances #-}

-- | Type classes 'Functor', 'Foldable', and 'Traversable' that correspond to the standard type classes of the same
-- name, but applying the given transformation to the given tree node and all its descendants. The corresponding classes
-- in the "Transformation.Shallow" moduleo perate only on the immediate children, while those from the
-- "Transformation.Deep" module exclude the argument node itself.

module Transformation.Full where

import Data.Coerce (Coercible)
import qualified Data.Functor
import           Data.Functor.Compose (Compose(getCompose))
import           Data.Functor.Const (Const(getConst))
import qualified Data.Foldable
import qualified Data.Traversable
import qualified Rank2
import qualified Transformation
import           Transformation (Transformation, Domain, Codomain)
import {-# SOURCE #-} qualified Transformation.Deep as Deep
import Unsafe.Coerce (unsafeCoerce)

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

-- | Like "Transformation.Deep".'Deep.Functor' except it maps an additional wrapper around the entire tree
class (Transformation t, Rank2.Functor (g (Domain t))) => Functor t g where
   (<$>) :: t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
   -- | Equivalent to @(Transformation.Coercion <$>)@ but faster
   coerce :: (t ~ Transformation.Coercion p q, forall h. Coercible (p (h p p)) (q (h q q))) => p (g p p) -> q (g q q)
   coerce = unsafeCoerce
   infixl 4 <$>

-- | Like "Transformation.Deep".'Deep.Foldable' except the entire tree is also wrapped
class (Transformation t, Rank2.Foldable (g (Domain t))) => Foldable t g where
   foldMap :: (Codomain t ~ Const m, Monoid m) => t -> Domain t (g (Domain t) (Domain t)) -> m

-- | Like "Transformation.Deep".'Deep.Traversable' except it traverses an additional wrapper around the entire tree
class (Transformation t, Rank2.Traversable (g (Domain t))) => Traversable t g where
   traverse :: Codomain t ~ Compose m f => t -> Domain t (g (Domain t) (Domain t)) -> m (f (g f f))

-- | Transformation modifier that applies the transformation first to the tree and then to the wrapper
newtype Inward t = Inward t

-- | Transformation modifier that applies the transformation first to the wrapper and then to the tree
newtype Outward t = Outward t

instance Transformation t => Transformation (Inward t) where
  type Domain (Inward t) = Domain t
  type Codomain (Inward t) = Codomain t

instance Transformation t => Transformation (Outward t) where
  type Domain (Outward t) = Domain t
  type Codomain (Outward t) = Codomain t

instance t `Transformation.At` a => Inward t `Transformation.At` a where
  Inward t $ a = t Transformation.$ a

instance t `Transformation.At` a => Outward t `Transformation.At` a where
  Outward t $ a = t Transformation.$ a

instance (Deep.Functor (Inward t) g, t `Transformation.At` g (Codomain t) (Codomain t),
          Data.Functor.Functor (Domain t), Rank2.Functor (g (Domain t))) =>
         Functor (Inward t) g where
  (<$>) = mapUpDefault

instance (Deep.Functor (Outward t) g, t `Transformation.At` g (Domain t) (Domain t),
          Data.Functor.Functor (Codomain t), Rank2.Functor (g (Domain t))) =>
         Functor (Outward t) g where
  (<$>) = mapDownDefault

instance (Deep.Foldable (Inward t) g, t `Transformation.At` g (Domain t) (Domain t),
          Rank2.Foldable (g (Domain t)), Codomain t ~ Const m, Data.Foldable.Foldable (Domain t), Monoid m) =>
         Foldable (Inward t) g where
  foldMap = foldMapUpDefault

instance (Deep.Foldable (Outward t) g, t `Transformation.At` g (Domain t) (Domain t),
          Rank2.Foldable (g (Domain t)), Codomain t ~ Const m, Data.Foldable.Foldable (Domain t), Monoid m) =>
         Foldable (Outward t) g where
  foldMap = foldMapDownDefault

instance (Deep.Traversable (Inward t) g, Codomain t ~ Compose m f, t `Transformation.At` g f f,
          Rank2.Traversable (g (Domain t)), Data.Traversable.Traversable (Domain t), Monad m) =>
         Traversable (Inward t) g where
  traverse = traverseUpDefault

instance (Deep.Traversable (Outward t) g, Codomain t ~ Compose m f, t `Transformation.At` g (Domain t) (Domain t),
          Rank2.Traversable (g (Domain t)), Data.Traversable.Traversable f, Monad m) =>
         Traversable (Outward t) g where
  traverse = traverseDownDefault

-- | Alphabetical synonym for '<$>'
fmap :: Functor t g => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
fmap = (<$>)

-- | Default implementation for '<$>' that maps the wrapper and then the tree
mapDownDefault :: (Deep.Functor t g, t `Transformation.At` g (Domain t) (Domain t), Data.Functor.Functor (Codomain t))
               => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
mapDownDefault t x = (t Deep.<$>) Data.Functor.<$> (t Transformation.$ x)

-- | Default implementation for '<$>' that maps the tree and then the wrapper
mapUpDefault   :: (Deep.Functor t g, t `Transformation.At` g (Codomain t) (Codomain t), Data.Functor.Functor (Domain t))
               => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
mapUpDefault   t x = t Transformation.$ ((t Deep.<$>) Data.Functor.<$> x)

foldMapDownDefault, foldMapUpDefault :: (t `Transformation.At` g (Domain t) (Domain t), Deep.Foldable t g,
                                         Codomain t ~ Const m, Data.Foldable.Foldable (Domain t), Monoid m)
                                     => t -> Domain t (g (Domain t) (Domain t)) -> m
-- | Default implementation for 'foldMap' that folds the wrapper and then the tree
foldMapDownDefault t x = getConst (t Transformation.$ x) `mappend` Data.Foldable.foldMap (Deep.foldMap t) x
-- | Default implementation for 'foldMap' that folds the tree and then the wrapper
foldMapUpDefault   t x = Data.Foldable.foldMap (Deep.foldMap t) x `mappend` getConst (t Transformation.$ x)

-- | Default implementation for 'traverse' that traverses the wrapper and then the tree
traverseDownDefault :: (Deep.Traversable t g, t `Transformation.At` g (Domain t) (Domain t),
                        Codomain t ~ Compose m f, Data.Traversable.Traversable f, Monad m)
                    => t -> Domain t (g (Domain t) (Domain t)) -> m (f (g f f))
traverseDownDefault t x = getCompose (t Transformation.$ x) >>= Data.Traversable.traverse (Deep.traverse t)

-- | Default implementation for 'traverse' that traverses the tree and then the wrapper
traverseUpDefault   :: (Deep.Traversable t g, Codomain t ~ Compose m f, t `Transformation.At` g f f,
                        Data.Traversable.Traversable (Domain t), Monad m)
                    => t -> Domain t (g (Domain t) (Domain t)) -> m (f (g f f))
traverseUpDefault   t x = Data.Traversable.traverse (Deep.traverse t) x >>= getCompose . (t Transformation.$)
