{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, TypeFamilies, TypeOperators #-}

module Transformation.Full where

import qualified Data.Functor
import           Data.Functor.Compose (Compose(Compose, getCompose))
import           Data.Kind (Type)
import qualified Data.Traversable
import qualified Transformation
import           Transformation (Transformation, Domain, Codomain)
import {-# SOURCE #-} qualified Transformation.Deep as Deep

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Transformation t => Functor t g where
   (<$>) :: t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))

class Transformation t => Traversable t g where
   traverse :: Codomain t ~ Compose m f => t -> Domain t (g (Domain t) (Domain t)) -> m (f (g f f))

fmap :: Functor t g => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
fmap = (<$>)

mapDownDefault :: (Deep.Functor t g, t `Transformation.At` g (Domain t) (Domain t), Data.Functor.Functor (Codomain t))
               => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
mapUpDefault   :: (Deep.Functor t g, t `Transformation.At` g (Codomain t) (Codomain t), Data.Functor.Functor (Domain t))
               => t -> Domain t (g (Domain t) (Domain t)) -> Codomain t (g (Codomain t) (Codomain t))
mapDownDefault t x = (t Deep.<$>) Data.Functor.<$> (Transformation.apply t x)
mapUpDefault   t x = Transformation.apply t ((t Deep.<$>) Data.Functor.<$> x)

traverseDownDefault :: (Deep.Traversable t g, t `Transformation.At` g (Domain t) (Domain t),
                        Codomain t ~ Compose m f, Data.Traversable.Traversable f, Monad m)
                    => t -> Domain t (g (Domain t) (Domain t)) -> m (f (g f f))
traverseUpDefault   :: (Deep.Traversable t g, Codomain t ~ Compose m f, t `Transformation.At` g f f,
                        Data.Traversable.Traversable (Domain t), Monad m)
                    => t -> Domain t (g (Domain t) (Domain t)) -> m (f (g f f))
traverseDownDefault t x = getCompose (Transformation.apply t x) >>= Data.Traversable.traverse (Deep.traverse t)
traverseUpDefault   t x = Data.Traversable.traverse (Deep.traverse t) x >>= getCompose . Transformation.apply t
