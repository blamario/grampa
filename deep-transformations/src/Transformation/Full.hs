{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}

module Transformation.Full where

import Control.Applicative ((<*>), liftA2)
import Data.Data (Data, Typeable)
import Data.Monoid (Monoid, (<>))
import qualified Rank2
import qualified Data.Foldable
import qualified Data.Functor
import qualified Data.Traversable
import qualified Transformation as Shallow
import           Transformation (Transformation, Domain, Codomain)
import {-# SOURCE #-} qualified Transformation.Deep as Deep

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Transformation t => Functor t g where
   (<$>) :: t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))

class Transformation t => Foldable t g m where
   foldMap :: t -> Domain t (g (Domain t) (Domain t)) -> m

class Transformation t => Traversable t g m where
   traverse :: t -> Domain t (g (Domain t) (Domain t)) -> m (Codomain t (g (Codomain t) (Codomain t)))

fmap :: Functor t g => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
fmap = (<$>)

mapDownDefault :: (Deep.Functor t g, Shallow.Functor t (g (Domain t) (Domain t)), Data.Functor.Functor (Codomain t))
               => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
mapUpDefault   :: (Deep.Functor t g, Shallow.Functor t (g (Codomain t) (Codomain t)), Data.Functor.Functor (Domain t))
               => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
mapDownDefault t x = (t Deep.<$>) Data.Functor.<$> (t Shallow.<$> x)
mapUpDefault   t x = t Shallow.<$> ((t Deep.<$>) Data.Functor.<$> x)

foldMapDefault :: (Deep.Foldable t g m, Data.Foldable.Foldable (Domain t), Monoid m) => t -> Domain t (g (Domain t) (Domain t)) -> m
foldMapDefault t x = Data.Foldable.foldMap (Deep.foldMap t) x

traverseDownDefault :: (Deep.Traversable t g m, Shallow.Traversable t m (g (Domain t) (Domain t)),
                        Data.Traversable.Traversable (Codomain t), Monad m)
                    => t -> Domain t (g (Domain t) (Domain t)) -> m (Codomain t (g (Codomain t) (Codomain t)))
traverseUpDefault   :: (Deep.Traversable t g m, Shallow.Traversable t m (g (Codomain t) (Codomain t)),
                        Data.Traversable.Traversable (Domain t), Monad m)
                    => t -> Domain t (g (Domain t) (Domain t)) -> m (Codomain t (g (Codomain t) (Codomain t)))
traverseDownDefault t x = Shallow.traverse t x >>= Data.Traversable.traverse (Deep.traverse t)
traverseUpDefault   t x = Data.Traversable.traverse (Deep.traverse t) x >>= Shallow.traverse t
