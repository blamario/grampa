{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}

module Transformation.Full where

import qualified Data.Functor
import           Data.Kind (Type)
import qualified Data.Traversable
import qualified Transformation as Shallow
import           Transformation (Transformation, TraversableTransformation, Domain, Codomain, Algebra)
import {-# SOURCE #-} qualified Transformation.Deep as Deep

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Transformation t => Functor t g where
   (<$>) :: t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))

class TraversableTransformation t => Traversable t g where
   traverse :: t -> Domain t (g (Domain t) (Domain t)) -> Algebra t (Codomain t (g (Codomain t) (Codomain t)))

fmap :: Functor t g => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
fmap = (<$>)

mapDownDefault :: (Deep.Functor t g, Shallow.Functor t (g (Domain t) (Domain t)), Data.Functor.Functor (Codomain t))
               => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
mapUpDefault   :: (Deep.Functor t g, Shallow.Functor t (g (Codomain t) (Codomain t)), Data.Functor.Functor (Domain t))
               => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
mapDownDefault t x = (t Deep.<$>) Data.Functor.<$> (t Shallow.<$> x)
mapUpDefault   t x = t Shallow.<$> ((t Deep.<$>) Data.Functor.<$> x)

traverseDownDefault :: (Deep.Traversable t g, Shallow.Traversable t (g (Domain t) (Domain t)),
                        Data.Traversable.Traversable (Codomain t), Monad (Algebra t))
                    => t -> Domain t (g (Domain t) (Domain t))
                       -> Algebra t (Codomain t (g (Codomain t) (Codomain t)))
traverseUpDefault   :: (Deep.Traversable t g, Shallow.Traversable t (g (Codomain t) (Codomain t)),
                        Data.Traversable.Traversable (Domain t), Monad (Algebra t))
                    => t -> Domain t (g (Domain t) (Domain t))
                       -> Algebra t (Codomain t (g (Codomain t) (Codomain t)))
traverseDownDefault t x = Shallow.traverse t x >>= Data.Traversable.traverse (Deep.traverse t)
traverseUpDefault   t x = Data.Traversable.traverse (Deep.traverse t) x >>= Shallow.traverse t
