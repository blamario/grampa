{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, StandaloneDeriving,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation.AG where

import Data.Functor.Identity
import qualified Rank2
import Transformation (Transformation, Domain, Codomain)
import qualified Transformation
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

instance Transformation (Inherited t a) where
   type Domain (Inherited t a) = Semantics t
   type Codomain (Inherited t a) = Inherited t

instance (Atts (Inherited t) a ~ Atts (Inherited t) b) => Transformation.Functor (Inherited t a) b where
   Inherited i <$> _ = Inherited i

passDown :: (sem ~ Semantics t, Shallow.Functor (Inherited t (g sem sem)) (g sem)) =>
            Inherited t (g sem sem) -> g sem sem -> g sem (Inherited t)
passDown inheritance node = inheritance Shallow.<$> node

-- | Drop-in implementation of 'Transformation.<$>'
mapDefault :: (q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Attribution t g p)
           => (p x -> x) -> t -> p x -> q x
mapDefault getSemantics t x = knit (attribution t x) (getSemantics x)
{-# INLINE mapDefault #-}
