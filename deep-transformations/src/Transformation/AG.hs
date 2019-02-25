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

class Attribution t g local where
   attribution :: t -> local -> Rule t g

-- | Drop-in implementation of 'Transformation.<$>'
mapDefault :: (q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Attribution t g local)
           => (p x -> local) -> (p x -> x) -> t -> p x -> q x
mapDefault getLocal getSemantics t x = knit (attribution t $ getLocal x) (getSemantics x)
{-# INLINE mapDefault #-}
