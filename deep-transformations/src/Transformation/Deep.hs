{-# Language DeriveDataTypeable, FlexibleInstances, KindSignatures, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | Type classes 'Functor', 'Foldable', and 'Traversable' that correspond to the standard type classes of the same
-- name, but applying the given transformation to every descendant of the given tree node. The corresponding classes
-- in the "Transformation.Shallow" module operate only on the immediate children, while those from the
-- "Transformation.Full" module include the argument node itself.

module Transformation.Deep where

import Control.Applicative (Applicative, liftA2)
import Data.Data (Data, Typeable)
import Data.Functor.Compose (Compose)
import Data.Functor.Const (Const)
import qualified Data.Functor as Rank1
import qualified Data.Functor
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

-- | Like 'Data.Functor.Product.Product' for data types with two type constructor parameters
data Product g h (d :: Type -> Type) (s :: Type -> Type) =
   Pair{fst :: s (g d d),
        snd :: s (h d d)}

-- | Like 'Data.Functor.Sum.Sum' for data types with two type constructor parameters
data Sum g h (d :: Type -> Type) (s :: Type -> Type) =
   InL (s (g d d))
   | InR (s (h d d))

instance Rank2.Functor (Product g h p) where
   f <$> ~(Pair left right) = Pair (f left) (f right)

instance Rank2.Apply (Product g h p) where
   ~(Pair g1 h1) <*> ~(Pair g2 h2) = Pair (Rank2.apply g1 g2) (Rank2.apply h1 h2)
   liftA2 f ~(Pair g1 h1) ~(Pair g2 h2) = Pair (f g1 g2) (f h1 h2)

instance Rank2.Applicative (Product g h p) where
   pure f = Pair f f

instance Rank2.Foldable (Product g h p) where
   foldMap f ~(Pair g h) = f g `mappend` f h

instance Rank2.Traversable (Product g h p) where
   traverse f ~(Pair g h) = liftA2 Pair (f g) (f h)

instance Rank2.DistributiveTraversable (Product g h p)

instance Rank2.Distributive (Product g h p) where
   cotraverse w f = Pair{fst= w (fst Data.Functor.<$> f),
                         snd= w (snd Data.Functor.<$> f)}

instance (Full.Functor t g, Full.Functor t h) => Functor t (Product g h) where
   t <$> Pair left right = Pair (t Full.<$> left) (t Full.<$> right)

instance (Full.Traversable t g, Full.Traversable t h, Codomain t ~ Compose m f, Applicative m) =>
         Traversable t (Product g h) where
   traverse t (Pair left right) = liftA2 Pair (Full.traverse t left) (Full.traverse t right)

deriving instance (Typeable p, Typeable q, Typeable g1, Typeable g2,
                   Data (q (g1 p p)), Data (q (g2 p p))) => Data (Product g1 g2 p q)
deriving instance (Show (q (g1 p p)), Show (q (g2 p p))) => Show (Product g1 g2 p q)

instance Rank2.Functor (Sum g h p) where
   f <$> InL left = InL (f left)
   f <$> InR right = InR (f right)

instance Rank2.Foldable (Sum g h p) where
   foldMap f (InL left) = f left
   foldMap f (InR right) = f right

instance Rank2.Traversable (Sum g h p) where
   traverse f (InL left) = InL Rank1.<$> f left
   traverse f (InR right) = InR Rank1.<$> f right

instance (Full.Functor t g, Full.Functor t h) => Functor t (Sum g h) where
   t <$> InL left = InL (t Full.<$> left)
   t <$> InR right = InR (t Full.<$> right)

instance (Full.Foldable t g, Full.Foldable t h, Codomain t ~ Const m) => Foldable t (Sum g h) where
   foldMap t (InL left) = Full.foldMap t left
   foldMap t (InR right) = Full.foldMap t right

instance (Full.Traversable t g, Full.Traversable t h, Codomain t ~ Compose m f, Applicative m) =>
         Traversable t (Sum g h) where
   traverse t (InL left) = InL Rank1.<$> Full.traverse t left
   traverse t (InR right) = InR Rank1.<$> Full.traverse t right

deriving instance (Typeable p, Typeable q, Typeable g1, Typeable g2,
                   Data (q (g1 p p)), Data (q (g2 p p))) => Data (Sum g1 g2 p q)
deriving instance (Show (q (g1 p p)), Show (q (g2 p p))) => Show (Sum g1 g2 p q)

-- | Alphabetical synonym for '<$>'
fmap :: Functor t g => t -> g (Domain t) (Domain t) -> g (Codomain t) (Codomain t)
fmap = (<$>)

-- | Equivalent of 'Data.Either.either'
eitherFromSum :: Sum g h d s -> Either (s (g d d)) (s (h d d))
eitherFromSum (InL left) = Left left
eitherFromSum (InR right) = Right right
