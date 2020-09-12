{-# Language FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, RankNTypes, StandaloneDeriving,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation.AG where

import Data.Functor.Identity
import qualified Rank2
import Transformation (Transformation, Domain, Codomain)
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Shallow as Shallow

type family Atts (f :: * -> *) a

newtype Inherited t a = Inherited{inh :: Atts (Inherited t) a}
newtype Synthesized t a = Synthesized{syn :: Atts (Synthesized t) a}

deriving instance (Show (Atts (Inherited t) a)) => Show (Inherited t a)
deriving instance (Show (Atts (Synthesized t) a)) => Show (Synthesized t a)

type Semantics t = Inherited t Rank2.~> Synthesized t

type Rule t g =  forall sem . sem ~ Semantics t
              => (Inherited   t (g sem sem), g sem (Synthesized t))
              -> (Synthesized t (g sem sem), g sem (Inherited t))

knit :: (Rank2.Apply (g sem), sem ~ Semantics t) => Rule t g -> g sem sem -> sem (g sem sem)
knit r chSem = Rank2.Arrow knit'
   where knit' inh = syn
            where (syn, chInh) = r (inh, chSyn)
                  chSyn = chSem Rank2.<*> chInh

class Transformation t => Revelation t where
   reveal :: t -> Domain t x -> x

class Attribution t g deep shallow where
   attribution :: t -> shallow (g deep deep) -> Rule t g

class Bequether t g deep shallow where
   bequest     :: forall sem. sem ~ Semantics t =>
                  t -> shallow (g deep deep)
               -> Atts (Inherited t) (g sem sem)
               -> g sem (Synthesized t)
               -> g sem (Inherited t)

class Synthesizer t g deep shallow where
   synthesis   :: forall sem. sem ~ Semantics t =>
                  t -> shallow (g deep deep)
               -> Atts (Inherited t) (g sem sem)
               -> g sem (Synthesized t)
               -> Atts (Synthesized t) (g sem sem)

newtype Auto t = Auto t

instance (Bequether (Auto t) g d s, sem ~ Semantics (Auto t), Synthesizer (Auto t) g d s) =>
         Attribution (Auto t) g d s where
   attribution t l (Inherited i, s) = (Synthesized $ synthesis t l i s, bequest t l i s)

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Attribution t g q p)
             => (forall a. p a -> a) -> t -> p x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Full.<$>'
fullMapDefault :: (p ~ Domain t, q ~ Semantics t, q ~ Codomain t, x ~ g q q, Rank2.Apply (g q),
                   Deep.Functor t g, Attribution t g p p)
               => (forall a. p a -> a) -> t -> p (g p p) -> q (g q q)
fullMapDefault extract t local = knit (attribution t local) (t Deep.<$> extract local)
{-# INLINE fullMapDefault #-}
