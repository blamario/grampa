{-# Language FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, StandaloneDeriving,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | An attribute grammar is a particular kind of 'Transformation' that assigns attributes to nodes in a
-- tree. Different node types may have different types of attributes, so the transformation is not natural. All
-- attributes are divided into 'Inherited' and 'Synthesized' attributes.

module Transformation.AG where

import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)

import qualified Rank2
import qualified Transformation

-- | Type family that maps a node type to the type of its attributes, indexed per type constructor.
type family Atts (f :: Type -> Type) a

-- | Type constructor wrapping the inherited attributes for the given transformation.
newtype Inherited t a = Inherited{inh :: Atts (Inherited t) a}
-- | Type constructor wrapping the synthesized attributes for the given transformation.
newtype Synthesized t a = Synthesized{syn :: Atts (Synthesized t) a}

deriving instance (Show (Atts (Inherited t) a)) => Show (Inherited t a)
deriving instance (Show (Atts (Synthesized t) a)) => Show (Synthesized t a)

-- | A node's 'Semantics' is a natural tranformation from the node's inherited attributes to its synthesized
-- attributes.
type Semantics t = Inherited t Rank2.~> Synthesized t

-- | A node's 'PreservingSemantics' is a natural tranformation from the node's inherited attributes to all its
-- attributes paired with the preserved node.
type PreservingSemantics t f = Rank2.Arrow (Inherited t) (Rank2.Product (AllAtts t) f)

-- | All inherited and synthesized attributes
data AllAtts t a = AllAtts{allInh :: Atts (Inherited t) a,
                           allSyn :: Atts (Synthesized t) a}

-- | An attribution rule maps a node's inherited attributes and its child nodes' synthesized attributes to the node's
-- synthesized attributes and the children nodes' inherited attributes.
type Rule t g =  forall sem . sem ~ Semantics t
              => (Inherited   t (g sem (Semantics t)), g sem (Synthesized t))
              -> (Synthesized t (g sem (Semantics t)), g sem (Inherited t))

-- | The core function to tie the recursive knot, turning a 'Rule' for a node into its 'Semantics'.
knit :: (Rank2.Apply (g sem), sem ~ Semantics t) => Rule t g -> g sem sem -> sem (g sem sem)
knit r chSem = Rank2.Arrow knit'
   where knit' inherited = synthesized
            where (synthesized, chInh) = r (inherited, chSyn)
                  chSyn = chSem Rank2.<*> chInh

-- | Another way to tie the recursive knot, using a 'Rule' to add 'AllAtts' information to every node
knitKeeping :: forall t f g sem. (sem ~ PreservingSemantics t f, Rank2.Apply (g sem),
                              Atts (Inherited t) (g sem sem) ~ Atts (Inherited t) (g (Semantics t) (Semantics t)),
                              Atts (Synthesized t) (g sem sem) ~ Atts (Synthesized t) (g (Semantics t) (Semantics t)),
                              g sem (Synthesized t) ~ g (Semantics t) (Synthesized t),
                              g sem (Inherited t) ~ g (Semantics t) (Inherited t))
            => (forall a. f a -> a) -> Rule t g -> f (g (PreservingSemantics t f) (PreservingSemantics t f))
            -> PreservingSemantics t f (g (PreservingSemantics t f) (PreservingSemantics t f))
knitKeeping extract rule x = Rank2.Arrow knitted
   where knitted :: Inherited t (g (PreservingSemantics t f) (PreservingSemantics t f))
                 -> Rank2.Product (AllAtts t) f (g (PreservingSemantics t f) (PreservingSemantics t f))
         chSem :: g (PreservingSemantics t f) (PreservingSemantics t f)
         knitted inherited = Rank2.Pair AllAtts{allInh= inh inherited, allSyn= syn synthesized} x
            where chInh :: g (PreservingSemantics t f) (Inherited t)
                  chSyn :: g (PreservingSemantics t f) (Synthesized t)
                  chKept :: g (PreservingSemantics t f) (Rank2.Product (AllAtts t) f)
                  synthesized :: Synthesized t (g (PreservingSemantics t f) (PreservingSemantics t f))
                  (synthesized, chInh) = unsafeCoerce (rule (unsafeCoerce inherited, unsafeCoerce chSyn))
                  chSyn = Synthesized . allSyn . Rank2.fst Rank2.<$> chKept
                  chKept = chSem Rank2.<*> chInh
         chSem = extract x

-- | The core type class for defining the attribute grammar. The instances of this class typically have a form like
--
-- > instance Attribution MyAttGrammar MyNode (Semantics MyAttGrammar) Identity where
-- >   attribution MyAttGrammar{} (Identity MyNode{})
-- >               (Inherited   fromParent,
-- >                Synthesized MyNode{firstChild= fromFirstChild, ...})
-- >             = (Synthesized _forMyself,
-- >                Inherited   MyNode{firstChild= _forFirstChild, ...})
--
-- If you prefer to separate the calculation of different attributes, you can split the above instance into two
-- instances of the 'Transformation.AG.Generics.Bequether' and 'Transformation.AG.Generics.Synthesizer' classes
-- instead. If you derive 'GHC.Generics.Generic' instances for your attributes, you can even define each synthesized
-- attribute individually with a 'Transformation.AG.Generics.SynthesizedField' instance.
class Attribution t g deep shallow where
   -- | The attribution rule for a given transformation and node.
   attribution :: t -> shallow (g deep deep) -> Rule t g

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Attribution t g q p)
             => (forall a. p a -> a) -> t -> p x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Transformation.$' that preserves all attributes with every original node
applyDefaultWithAttributes :: (p ~ Transformation.Domain t, q ~ PreservingSemantics t p, x ~ g q q, Rank2.Apply (g q),
                               Atts (Inherited t) (g q q) ~ Atts (Inherited t) (g (Semantics t) (Semantics t)),
                               Atts (Synthesized t) (g q q) ~ Atts (Synthesized t) (g (Semantics t) (Semantics t)),
                               g q (Synthesized t) ~ g (Semantics t) (Synthesized t),
                               g q (Inherited t) ~ g (Semantics t) (Inherited t),
                               Attribution t g (PreservingSemantics t p) p)
                           => (forall a. p a -> a) -> t -> p (g (PreservingSemantics t p) (PreservingSemantics t p))
                           -> PreservingSemantics t p (g (PreservingSemantics t p) (PreservingSemantics t p))
applyDefaultWithAttributes extract t x = knitKeeping extract (attribution t x) x
{-# INLINE applyDefaultWithAttributes #-}
