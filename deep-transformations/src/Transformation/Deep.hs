{-# Language DeriveDataTypeable, FlexibleInstances, KindSignatures, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, UndecidableInstances #-}

module Transformation.Deep where

import Control.Applicative ((<*>), liftA2)
import Data.Data (Data, Typeable)
import Data.Monoid (Monoid, (<>))
import qualified Rank2
import qualified Data.Foldable
import qualified Data.Functor
import qualified Data.Traversable
import qualified Transformation as Shallow

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Rank2.Functor (g p) => Functor t g (p :: * -> *) (q :: * -> *) where
   (<$>) :: t -> g p p -> g q q

class Rank2.Foldable (g p) => Foldable t g p m where
   foldMap :: t -> g p p -> m

class Rank2.Traversable (g p) => UpTraversable t g (p :: * -> *) (q :: * -> *) m where
   traverseUp :: t -> g p p -> m (g q q)

class Rank2.Traversable (g p) => DownTraversable t g (p :: * -> *) (q :: * -> *) m where
   traverseDown :: t -> g p p -> m (g q q)

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

instance (Data.Functor.Functor p, Shallow.Functor t p q (g1 q q), Shallow.Functor t p q (g2 q q),
          Functor t g1 p q, Functor t g2 p q) => Functor t (Product g1 g2) p q where
   t <$> Pair left right = Pair (t Shallow.<$> ((t <$>) Data.Functor.<$> left)) 
                                (t Shallow.<$> ((t <$>) Data.Functor.<$> right))

instance (Monoid m, Data.Foldable.Foldable p,
          Foldable t g1 p m, Foldable t g2 p m) => Foldable t (Product g1 g2) p m where
   foldMap t (Pair left right) = Data.Foldable.foldMap (foldMap t) left
                                 <> Data.Foldable.foldMap (foldMap t) right

instance (Monad m, Data.Traversable.Traversable p,
          Shallow.Traversable t p q m (g1 q q), Shallow.Traversable t p q m (g2 q q),
          UpTraversable t g1 p q m, UpTraversable t g2 p q m) => UpTraversable t (Product g1 g2) p q m where
   traverseUp t (Pair left right) =
      Pair        Data.Functor.<$> (Data.Traversable.traverse (traverseUp t) left >>= Shallow.traverse t)
           Control.Applicative.<*> (Data.Traversable.traverse (traverseUp t) right >>= Shallow.traverse t)

instance (Monad m, Data.Traversable.Traversable q,
          Shallow.Traversable t p q m (g1 p p), Shallow.Traversable t p q m (g2 p p),
          DownTraversable t g1 p q m, DownTraversable t g2 p q m) => DownTraversable t (Product g1 g2) p q m where
   traverseDown t (Pair left right) =
      Pair        Data.Functor.<$> (Shallow.traverse t left >>= Data.Traversable.traverse (traverseDown t))
           Control.Applicative.<*> (Shallow.traverse t right >>= Data.Traversable.traverse (traverseDown t))

deriving instance (Typeable p, Typeable q, Typeable g1, Typeable g2,
                   Data (q (g1 p p)), Data (q (g2 p p))) => Data (Product g1 g2 p q)
deriving instance (Show (q (g1 p p)), Show (q (g2 p p))) => Show (Product g1 g2 p q)

fmap :: Functor t g p q => t -> g p p -> g q q
fmap = (<$>)
