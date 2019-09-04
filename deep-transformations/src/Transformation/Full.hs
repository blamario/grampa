{-# Language FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}

module Transformation.Full where

import Control.Applicative ((<*>), liftA2)
import Data.Data (Data, Typeable)
import Data.Monoid (Monoid, (<>))
import qualified Rank2
import qualified Data.Foldable
import qualified Data.Functor
import qualified Data.Traversable
import qualified Transformation as Shallow
import {-# SOURCE #-} qualified Transformation.Deep as Deep

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Functor t g p q where
   (<$>) :: t -> p (g p p) -> q (g q q)

class Foldable t g p m where
   foldMap :: t -> p (g p p) -> m

class Traversable t g p q m where
   traverse :: t -> p (g p p) -> m (q (g q q))

fmap :: Functor t g p q => t -> p (g p p) -> q (g q q)
fmap = (<$>)

mapDownDefault :: (Deep.Functor t g p q, Shallow.Functor t p q (g p p), Data.Functor.Functor q)
               => t -> p (g p p) -> q (g q q)
mapUpDefault   :: (Deep.Functor t g p q, Shallow.Functor t p q (g q q), Data.Functor.Functor p)
               => t -> p (g p p) -> q (g q q)
mapDownDefault t x = (t Deep.<$>) Data.Functor.<$> (t Shallow.<$> x)
mapUpDefault   t x = t Shallow.<$> ((t Deep.<$>) Data.Functor.<$> x)

foldMapDefault :: (Deep.Foldable t g p m, Data.Foldable.Foldable p, Monoid m) => t -> p (g p p) -> m
foldMapDefault t x = Data.Foldable.foldMap (Deep.foldMap t) x

traverseDownDefault :: (Deep.Traversable t g p q m, Shallow.Traversable t p q m (g p p),
                        Data.Traversable.Traversable q, Monad m)
                    => t -> p (g p p) -> m (q (g q q))
traverseUpDefault   :: (Deep.Traversable t g p q m, Shallow.Traversable t p q m (g q q),
                        Data.Traversable.Traversable p, Monad m)
                    => t -> p (g p p) -> m (q (g q q))
traverseDownDefault t x = Shallow.traverse t x >>= Data.Traversable.traverse (Deep.traverse t)
traverseUpDefault   t x = Data.Traversable.traverse (Deep.traverse t) x >>= Shallow.traverse t
