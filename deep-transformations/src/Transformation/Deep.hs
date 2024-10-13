{-# Language Haskell2010, DeriveDataTypeable, FlexibleInstances, KindSignatures, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | Type classes 'Functor', 'Foldable', and 'Traversable' that correspond to the standard type classes of the same
-- name, but applying the given transformation to every descendant of the given tree node. The corresponding classes
-- in the "Transformation.Shallow" module operate only on the immediate children, while those from the
-- "Transformation.Full" module include the argument node itself.

module Transformation.Deep where

import Data.Data (Data, Typeable)
import Data.Functor.Compose (Compose)
import Data.Functor.Const (Const)
import qualified Control.Applicative as Rank1
import qualified Data.Foldable as Rank1
import qualified Data.Functor as Rank1
import qualified Data.Traversable as Rank1
import Data.Kind (Type)
import qualified Rank2
import           Transformation (Transformation, Domain, Codomain)
import qualified Transformation.Full as Full

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

-- | Like "Transformation.Shallow".'Transformation.Shallow.Functor' except it maps all descendants and not only immediate children
class (Transformation t, Rank2.Functor (g (Domain t))) => Functor t g where
   (<$>) :: t -> g (Domain t) (Domain t) -> g (Codomain t) (Codomain t)
   infixl 4 <$>

-- | Like "Transformation.Shallow".'Transformation.Shallow.Foldable' except it folds all descendants and not only immediate children
class (Transformation t, Rank2.Foldable (g (Domain t))) => Foldable t g where
   foldMap :: (Codomain t ~ Const m, Monoid m) => t -> g (Domain t) (Domain t) -> m

-- | Like "Transformation.Shallow".'Transformation.Shallow.Traversable' except it folds all descendants and not only immediate children
class (Transformation t, Rank2.Traversable (g (Domain t))) => Traversable t g where
   traverse :: Codomain t ~ Compose m f => t -> g (Domain t) (Domain t) -> m (g f f)

-- | A tuple of only one element
newtype Only g (d :: Type -> Type) (s :: Type -> Type) =
   Only {fromOnly :: s (g d d)}

-- | Compose a regular type constructor with a data type with two type constructor parameters
newtype Nest (f :: Type -> Type) g (d :: Type -> Type) (s :: Type -> Type) =
   Nest {unNest :: f (g d s)}

-- | Like 'Data.Functor.Product.Product' for data types with two type constructor parameters
data Product g h (d :: Type -> Type) (s :: Type -> Type) =
   Pair{fst :: g d s,
        snd :: h d s}

-- | Like 'Data.Functor.Sum.Sum' for data types with two type constructor parameters
data Sum g h (d :: Type -> Type) (s :: Type -> Type) =
   InL (g d s)
   | InR (h d s)

-- Instances

instance Rank2.Functor (Only g d) where
   f <$> Only x = Only (f x)

instance Rank2.Foldable (Only g d) where
   foldMap f (Only x) = f x

instance Rank2.Traversable (Only g d) where
   traverse f (Only x) = Only Rank1.<$> f x

instance Rank2.Apply (Only g d) where
   Only f <*> Only x = Only (Rank2.apply f x)
   liftA2 f (Only x) (Only y) = Only (f x y)

instance Rank2.Applicative (Only g d) where
   pure f = Only f

instance Rank2.DistributiveTraversable (Only g d)

instance Rank2.Distributive (Only g d) where
   cotraverse w f = Only (w (Rank1.fmap fromOnly f))

instance Full.Functor t g => Functor t (Only g) where
   t <$> Only x = Only (t Full.<$> x)

instance Full.Foldable t g => Foldable t (Only g) where
   foldMap t (Only x) = Full.foldMap t x

instance (Full.Traversable t g, Codomain t ~ Compose m f, Rank1.Functor m) => Traversable t (Only g) where
   traverse t (Only x) = Only Rank1.<$> Full.traverse t x

deriving instance (Typeable s, Typeable d, Typeable g, Data (s (g d d))) => Data (Only g d s)
deriving instance Eq (s (g d d)) => Eq (Only g d s)
deriving instance Ord (s (g d d)) => Ord (Only g d s)
deriving instance Show (s (g d d)) => Show (Only g d s)

instance (Rank1.Functor f, Rank2.Functor (g d)) => Rank2.Functor (Nest f g d) where
   f <$> Nest x = Nest ((f Rank2.<$>) Rank1.<$> x)

instance (Rank1.Applicative f, Rank2.Apply (g d)) => Rank2.Apply (Nest f g d) where
   Nest x <*> Nest y = Nest (Rank1.liftA2 (Rank2.<*>) x y)

instance (Rank1.Applicative f, Rank2.Applicative (g d)) => Rank2.Applicative (Nest f g d) where
   pure f = Nest (Rank1.pure (Rank2.pure f))

instance (Rank1.Foldable f, Rank2.Foldable (g d)) => Rank2.Foldable (Nest f g d) where
   foldMap f (Nest x) = Rank1.foldMap (Rank2.foldMap f) x

instance (Rank1.Traversable f, Rank2.Traversable (g d)) => Rank2.Traversable (Nest f g d) where
   traverse f (Nest x) = Nest Rank1.<$> Rank1.traverse (Rank2.traverse f) x

instance (Rank1.Functor f, Functor t g) => Functor t (Nest f g) where
   t <$> Nest x = Nest ((t <$>) Rank1.<$> x)

instance (Rank1.Foldable f, Foldable t g) => Foldable t (Nest f g) where
   foldMap t (Nest x) = Rank1.foldMap (foldMap t) x

instance (Rank1.Traversable f, Traversable t g, Codomain t ~ Compose m f, Rank1.Applicative m) =>
         Traversable t (Nest f g) where
   traverse t (Nest x) = Nest Rank1.<$> Rank1.traverse (traverse t) x

deriving instance (Typeable s, Typeable d, Typeable f, Typeable g,
                   Data (f (g d s))) => Data (Nest f g d s)
deriving instance Eq (f (g d s)) => Eq (Nest f g d s)
deriving instance Ord (f (g d s)) => Ord (Nest f g d s)
deriving instance Show (f (g d s)) => Show (Nest f g d s)

instance (Rank2.Functor (g d), Rank2.Functor (h d)) => Rank2.Functor (Product g h d) where
   f <$> (Pair left right) = Pair (f Rank2.<$> left) (f Rank2.<$> right)

instance (Rank2.Apply (g d), Rank2.Apply (h d)) => Rank2.Apply (Product g h d) where
   Pair g1 h1 <*> ~(Pair g2 h2) = Pair (g1 Rank2.<*> g2) (h1 Rank2.<*> h2)
   liftA2 f (Pair g1 h1) ~(Pair g2 h2) = Pair (Rank2.liftA2 f g1 g2) (Rank2.liftA2 f h1 h2)
   liftA3 f (Pair g1 h1) ~(Pair g2 h2) ~(Pair g3 h3) = Pair (Rank2.liftA3 f g1 g2 g3) (Rank2.liftA3 f h1 h2 h3)

instance (Rank2.Applicative (g d), Rank2.Applicative (h d)) => Rank2.Applicative (Product g h d) where
   pure f = Pair (Rank2.pure f) (Rank2.pure f)

instance (Rank2.Foldable (g d), Rank2.Foldable (h d)) => Rank2.Foldable (Product g h d) where
   foldMap f (Pair g h) = Rank2.foldMap f g `mappend` Rank2.foldMap f h

instance (Rank2.Traversable (g d), Rank2.Traversable (h d)) => Rank2.Traversable (Product g h d) where
   traverse f (Pair g h) = Rank1.liftA2 Pair (Rank2.traverse f g) (Rank2.traverse f h)

instance (Rank2.Distributive (g d), Rank2.Distributive (h d)) => Rank2.DistributiveTraversable (Product g h d)

instance (Rank2.Distributive (g d), Rank2.Distributive (h d)) => Rank2.Distributive (Product g h d) where
   cotraverse w f = Pair{fst= Rank2.cotraverse w (fst Rank1.<$> f),
                         snd= Rank2.cotraverse w (snd Rank1.<$> f)}

instance (Functor t g, Functor t h) => Functor t (Product g h) where
   t <$> Pair left right = Pair (t <$> left) (t <$> right)

instance (Foldable t g, Foldable t h) => Foldable t (Product g h) where
   foldMap t (Pair g h) = foldMap t g `mappend` foldMap t h

instance (Traversable t g, Traversable t h, Codomain t ~ Compose m f, Rank1.Applicative m) =>
         Traversable t (Product g h) where
   traverse t (Pair left right) = Rank1.liftA2 Pair (traverse t left) (traverse t right)

deriving instance (Typeable d, Typeable s, Typeable g1, Typeable g2,
                   Data (g1 d s), Data (g2 d s)) => Data (Product g1 g2 d s)
deriving instance (Show (g1 d s), Show (g2 d s)) => Show (Product g1 g2 d s)
deriving instance (Eq (g d s), Eq (h d s)) => Eq (Product g h d s)
deriving instance (Ord (g d s), Ord (h d s)) => Ord (Product g h d s)

instance (Rank2.Functor (g d), Rank2.Functor (h d)) => Rank2.Functor (Sum g h d) where
   f <$> InL left = InL (f Rank2.<$> left)
   f <$> InR right = InR (f Rank2.<$> right)

instance (Rank2.Foldable (g d), Rank2.Foldable (h d)) => Rank2.Foldable (Sum g h d) where
   foldMap f (InL left) = Rank2.foldMap f left
   foldMap f (InR right) = Rank2.foldMap f right

instance (Rank2.Traversable (g d), Rank2.Traversable (h d)) => Rank2.Traversable (Sum g h d) where
   traverse f (InL left) = InL Rank1.<$> Rank2.traverse f left
   traverse f (InR right) = InR Rank1.<$> Rank2.traverse f right

instance (Functor t g, Functor t h) => Functor t (Sum g h) where
   t <$> InL left = InL (t <$> left)
   t <$> InR right = InR (t <$> right)

instance (Foldable t g, Foldable t h, Codomain t ~ Const m) => Foldable t (Sum g h) where
   foldMap t (InL left) = foldMap t left
   foldMap t (InR right) = foldMap t right

instance (Traversable t g, Traversable t h, Codomain t ~ Compose m f, Rank1.Applicative m) =>
         Traversable t (Sum g h) where
   traverse t (InL left) = InL Rank1.<$> traverse t left
   traverse t (InR right) = InR Rank1.<$> traverse t right

deriving instance (Typeable d, Typeable s, Typeable g1, Typeable g2,
                   Data (g1 d s), Data (g2 d s)) => Data (Sum g1 g2 d s)
deriving instance (Show (g1 d s), Show (g2 d s)) => Show (Sum g1 g2 d s)
deriving instance (Eq (g d s), Eq (h d s)) => Eq (Sum g h d s)
deriving instance (Ord (g d s), Ord (h d s)) => Ord (Sum g h d s)

-- | Alphabetical synonym for '<$>'
fmap :: Functor t g => t -> g (Domain t) (Domain t) -> g (Codomain t) (Codomain t)
fmap = (<$>)

-- | Equivalent of 'Data.Either.either'
eitherFromSum :: Sum g h d s -> Either (g d s) (h d s)
eitherFromSum (InL left) = Left left
eitherFromSum (InR right) = Right right
