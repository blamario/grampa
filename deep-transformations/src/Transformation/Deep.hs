{-# Language DeriveDataTypeable, FlexibleInstances, KindSignatures, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, UndecidableInstances #-}

module Transformation.Deep where

import Control.Applicative (Applicative, (<*>), liftA2)
import Data.Data (Data, Typeable)
import Data.Monoid (Monoid, (<>))
import qualified Rank2
import qualified Data.Foldable
import qualified Data.Functor
import qualified Data.Traversable
import qualified Transformation as Shallow
import           Transformation (Transformation, Domain, Codomain)
import qualified Transformation.Full as Full

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class (Transformation t, Rank2.Functor (g (Domain t))) => Functor t g where
   (<$>) :: t -> g (Domain t) (Domain t) -> g (Codomain t) (Codomain t)

class (Transformation t, Rank2.Foldable (g (Domain t))) => Foldable t g m where
   foldMap :: t -> g (Domain t) (Domain t) -> m

class (Transformation t, Rank2.Traversable (g (Domain t))) => Traversable t g m where
   traverse :: t -> g (Domain t) (Domain t) -> m (g (Codomain t) (Codomain t))

data Product g1 g2 (p :: * -> *) (q :: * -> *) = Pair{fst :: q (g1 p p),
                                                      snd :: q (g2 p p)}

instance Rank2.Functor (Product g1 g2 p) where
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

instance (Monoid m, Full.Foldable t g m, Full.Foldable t h m) => Foldable t (Product g h) m where
   foldMap t (Pair left right) = Full.foldMap t left <> Full.foldMap t right

instance (Applicative m, Full.Traversable t g m, Full.Traversable t h m) =>
         Traversable t (Product g h) m where
   traverse t (Pair left right) = liftA2 Pair (Full.traverse t left) (Full.traverse t right)

deriving instance (Typeable p, Typeable q, Typeable g1, Typeable g2,
                   Data (q (g1 p p)), Data (q (g2 p p))) => Data (Product g1 g2 p q)
deriving instance (Show (q (g1 p p)), Show (q (g2 p p))) => Show (Product g1 g2 p q)

fmap :: Functor t g => t -> g (Domain t) (Domain t) -> g (Codomain t) (Codomain t)
fmap = (<$>)
