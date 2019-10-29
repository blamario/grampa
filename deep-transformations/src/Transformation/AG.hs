{-# Language FlexibleContexts, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, TypeFamilies, TypeOperators,
             UndecidableInstances #-}

module Transformation.AG where

import Data.Functor.Identity
import qualified Rank2

type family Atts (f :: * -> *) x

newtype Inherited a g = Inherited{inh :: Atts (Inherited a) g}
newtype Synthesized a g = Synthesized{syn :: Atts (Synthesized a) g}

deriving instance (Show (Atts (Inherited a) g)) => Show (Inherited a g)
deriving instance (Show (Atts (Synthesized a) g)) => Show (Synthesized a g)

type Semantics a = Inherited a Rank2.~> Synthesized a

type Rule a g =  forall sem . sem ~ Semantics a
              => (Inherited   a (g sem sem), g sem (Synthesized a))
              -> (Synthesized a (g sem sem), g sem (Inherited a))

knit :: (Rank2.Apply (g sem), sem ~ Semantics a) => Rule a g -> g sem sem -> sem (g sem sem)
knit r chSem = Rank2.Arrow knit'
   where knit' inh = syn
            where (syn, chInh) = r (inh, chSyn)
                  chSyn = chSem Rank2.<*> chInh

class Attribution t g f where
   attribution :: t -> f (g (Semantics t) (Semantics t)) -> Rule t g
   bequest :: forall sem . sem ~ Semantics t =>
              t -> f (g sem sem) -> Atts (Inherited t) (g sem sem) -> g sem (Synthesized t)
              -> g sem (Inherited t)
   synthesis   :: forall sem . sem ~ Semantics t =>
                  t -> f (g sem sem) -> Atts (Inherited t) (g sem sem) -> g sem (Synthesized t)
               -> Atts (Synthesized t) (g sem sem)
   attribution t l (Inherited i, s) = (Synthesized $ synthesis t l i s, bequest t l i s)
   bequest t l i s = snd (attribution t l (Inherited i, s))
   synthesis t l i s = syn (fst $ attribution t l (Inherited i, s))
   {-# Minimal attribution | bequest, synthesis #-}

class Inheritable t g where
   passOnInheritance :: sem ~ Semantics t => Atts (Inherited t) (g sem sem) -> g sem sem -> g sem (Inherited t)

-- | Drop-in implementation of 'Transformation.<$>'
mapDefault :: (q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Attribution t g p)
           => (p x -> x) -> t -> p x -> q x
mapDefault getSemantics t x = knit (attribution t x) (getSemantics x)
{-# INLINE mapDefault #-}
