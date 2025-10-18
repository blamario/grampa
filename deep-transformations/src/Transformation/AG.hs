{-# Language FlexibleContexts, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving, ImpredicativeTypes,
             MultiParamTypeClasses, NamedFieldPuns, RankNTypes, ScopedTypeVariables, StandaloneDeriving,
             TypeApplications, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | An attribute grammar is a particular kind of 'Transformation' that assigns attributes to nodes in a
-- tree. Different node types may have different types of attributes, so the transformation is not natural. All
-- attributes are divided into 'Inherited' and 'Synthesized' attributes.

module Transformation.AG where

import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)

import qualified Rank2
import Transformation (Transformation, Domain, Codomain)
import Transformation.Deep (Const2)
import qualified Transformation.Deep as Deep

-- | Type family that maps a node type to the type of its attributes, indexed per type constructor.
type family Atts (f :: Type -> Type) (g :: (Type -> Type) -> (Type -> Type) -> Type)

-- | Type family that lops off the two type parameters
type family NodeConstructor (a :: Type) :: (Type -> Type) -> (Type -> Type) -> Type where
   NodeConstructor (g p q) = g
   NodeConstructor t = Const2 t

-- | Type constructor wrapping the inherited attributes for the given transformation.
newtype Inherited t a = Inherited{inh :: Atts (Inherited t) (NodeConstructor a)}
-- | Type constructor wrapping the synthesized attributes for the given transformation.
newtype Synthesized t a = Synthesized{syn :: Atts (Synthesized t) (NodeConstructor a)}

deriving instance (Show (Atts (Inherited t) (NodeConstructor a))) => Show (Inherited t a)
deriving instance (Show (Atts (Synthesized t) (NodeConstructor a))) => Show (Synthesized t a)
deriving instance (Semigroup (Atts (Inherited t) (NodeConstructor a))) => Semigroup (Inherited t a)
deriving instance (Semigroup (Atts (Synthesized t) (NodeConstructor a))) => Semigroup (Synthesized t a)
deriving instance (Monoid (Atts (Inherited t) (NodeConstructor a))) => Monoid (Inherited t a)
deriving instance (Monoid (Atts (Synthesized t) (NodeConstructor a))) => Monoid (Synthesized t a)

mapInherited :: (Atts (Inherited t) (NodeConstructor a) -> Atts (Inherited t) (NodeConstructor b))
             -> Inherited t a -> Inherited t b
mapInherited f (Inherited a) = Inherited (f a)

mapSynthesized :: (Atts (Synthesized t) (NodeConstructor a) -> Atts (Synthesized t) (NodeConstructor b))
               -> Synthesized t a -> Synthesized t b
mapSynthesized f (Synthesized a) = Synthesized (f a)

-- | A node's 'Semantics' is a natural tranformation from the node's inherited attributes to its synthesized
-- attributes.
type Semantics t = Inherited t Rank2.~> Synthesized t

-- | The core type class for defining the attribute grammar. The instances of this class typically have a form like
--
-- > instance Attribution MyAttGrammar MyNode Identity where
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
class Transformation t => Attribution t g where
   -- | The attribution rule for a given transformation and node.
   attribution :: forall sem. Rank2.Traversable (g sem)
               => t -> Domain t (g sem sem)
               -> (Inherited   t (g sem sem), g sem (Synthesized t))
               -> (Synthesized t (g sem sem), g sem (Inherited t))

-- | Transformation wrapper that keeps all the original tree nodes alongside their attributes
newtype Keep t = Keep t

data Kept t a = Kept{inherited   :: Atts (Inherited t) (NodeConstructor a),
                     synthesized :: Atts (Synthesized t) (NodeConstructor a),
                     original    :: Domain t a}

deriving instance (Show (Atts (Inherited t) (NodeConstructor a)),
                   Show (Atts (Synthesized t) (NodeConstructor a)),
                   Show (Domain t a)) => Show (Kept t a)

type instance Atts (Inherited (Keep t)) g = Atts (Inherited t) g
type instance Atts (Synthesized (Keep t)) g = Kept t (g (Kept t) (Kept t))

instance (Transformation t, Codomain t ~ Semantics t) => Transformation (Keep t) where
   type Domain (Keep t) = Domain t
   type Codomain (Keep t) = Semantics (Keep t)

instance (Domain t ~ f, Codomain t ~ Semantics t, Rank2.Functor (g (Semantics (Keep t))), Functor f, Attribution t g) =>
         Attribution (Keep t) g where
   attribution (Keep t) x (Inherited i, childSynthesis) = (Synthesized synthesis', childInheritance') where
      (Synthesized s, childInheritance) = attribution t x (Inherited i :: Inherited t (g sem sem),
                                                           resynthesize Rank2.<$> childSynthesis)
      resynthesize :: forall a. Synthesized (Keep t) a -> Synthesized t a
      resynthesize (Synthesized Kept{synthesized}) = Synthesized synthesized
      synthesis' :: Atts (Synthesized (Keep t)) g
      synthesis' = Kept i s ((unsafeCoerce @(g _ (Synthesized (Keep t))) childSynthesis :: g (Kept t) (Kept t)) <$ x)
      childInheritance' :: g sem (Inherited (Keep t))
      childInheritance' = unsafeCoerce @(g _ (Inherited t)) childInheritance

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

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Rank2.Traversable (g (Semantics t)), Attribution t g)
             => (forall a. Domain t a -> a) -> t -> Domain t x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Full.<$>'
fullMapDefault :: (Transformation t, f ~ Domain t, sem ~ Codomain t, sem ~ Semantics t, Deep.Functor t g,
                   Rank2.Apply (g sem), Rank2.Traversable (g sem), Attribution t g, Functor f)
               => (f a -> g f f) -> t -> f a -> sem (g sem sem)
fullMapDefault extract t x = knit (attribution t (y <$ x)) y
   where y = t Deep.<$> extract x
{-# INLINE fullMapDefault #-}
