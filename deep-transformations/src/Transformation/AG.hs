{-# Language FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, RankNTypes, StandaloneDeriving,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | An attribute grammar is a particular kind of 'Transformation' that assigns attributes to nodes in a
-- tree. Different node types may have different types of attributes, so the transformation is not natural. All
-- attributes are divided into 'Inherited' and 'Synthesized' attributes.

module Transformation.AG where

import Data.Functor.Identity
import qualified Rank2
import Transformation (Transformation, Domain, Codomain)
import qualified Transformation
import qualified Transformation.Deep as Deep

-- | Type family that assigns maps a node type to the type of its attributes, indexed per type constructor.
type family Atts (f :: * -> *) a

-- | Type constructor wrapping the inherited attributes for the given transformation.
newtype Inherited t a = Inherited{inh :: Atts (Inherited t) a}
-- | Type constructor wrapping the synthesized attributes for the given transformation.
newtype Synthesized t a = Synthesized{syn :: Atts (Synthesized t) a}

deriving instance (Show (Atts (Inherited t) a)) => Show (Inherited t a)
deriving instance (Show (Atts (Synthesized t) a)) => Show (Synthesized t a)

-- | A node's 'Semantics' is a natural tranformation from the node's inherited attributes to its synthesized
-- attributes.
type Semantics t = Inherited t Rank2.~> Synthesized t

-- | An attribution rule maps a node's inherited attributes and its child nodes' synthesized attributes to the node's
-- synthesized attributes and the children nodes' inherited attributes.
type Rule t g =  forall sem . sem ~ Semantics t
              => (Inherited   t (g sem sem), g sem (Synthesized t))
              -> (Synthesized t (g sem sem), g sem (Inherited t))

knit :: (Rank2.Apply (g sem), sem ~ Semantics t) => Rule t g -> g sem sem -> sem (g sem sem)
knit r chSem = Rank2.Arrow knit'
   where knit' inh = syn
            where (syn, chInh) = r (inh, chSyn)
                  chSyn = chSem Rank2.<*> chInh

class Attribution t g deep shallow where
   -- | The attribution rule for a given transormation and node.
   attribution :: t -> shallow (g deep deep) -> Rule t g

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Attribution t g q p)
             => (forall a. p a -> a) -> t -> p x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Transformation.Full.<$>'
fullMapDefault :: (p ~ Domain t, q ~ Semantics t, q ~ Codomain t, x ~ g q q, Rank2.Apply (g q),
                   Deep.Functor t g, Attribution t g p p)
               => (forall a. p a -> a) -> t -> p (g p p) -> q (g q q)
fullMapDefault extract t local = knit (attribution t local) (t Deep.<$> extract local)
{-# INLINE fullMapDefault #-}
