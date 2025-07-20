{-# Language FlexibleContexts, FlexibleInstances, GADTs, ImpredicativeTypes,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, StandaloneDeriving,
             TypeApplications, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | An attribute grammar is a particular kind of 'Transformation' that assigns attributes to nodes in a
-- tree. Different node types may have different types of attributes, so the transformation is not natural. All
-- attributes are divided into 'Inherited' and 'Synthesized' attributes.

module Transformation.AG where

import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)

import qualified Rank2
import qualified Transformation
import Transformation.Deep (Const2)

-- | Type family that maps a node type to the type of its attributes, indexed per type constructor.
type family Atts (f :: Type -> Type) (g :: (Type -> Type) -> (Type -> Type) -> Type)

type family NodeConstructor (a :: Type) :: (Type -> Type) -> (Type -> Type) -> Type where
   NodeConstructor (g p q) = g
   NodeConstructor t = Const2 t

-- | Type constructor wrapping the inherited attributes for the given transformation.
newtype Inherited t a = Inherited{inh :: Atts (Inherited t) (NodeConstructor a)}
-- | Type constructor wrapping the synthesized attributes for the given transformation.
newtype Synthesized t a = Synthesized{syn :: Atts (Synthesized t) (NodeConstructor a)}

deriving instance (Show (Atts (Inherited t) (NodeConstructor a))) => Show (Inherited t a)
deriving instance (Show (Atts (Synthesized t) (NodeConstructor a))) => Show (Synthesized t a)

-- | A node's 'Semantics' is a natural tranformation from the node's inherited attributes to its synthesized
-- attributes.
type Semantics t = Inherited t Rank2.~> Synthesized t

-- | A node's 'PreservingSemantics' is a natural tranformation from the node's inherited attributes to all its
-- attributes paired with the preserved node.
-- type PreservingSemantics t f = Rank2.Arrow (Inherited t) (Rank2.Product (AllAtts t) f)

-- | All inherited and synthesized attributes
data AllAtts t a where
   AllAtts :: a ~ g f f => {allInh :: Atts (Inherited t) g,
                            allSyn :: Atts (Synthesized t) g} -> AllAtts t a

-- | An attribution rule maps a node's inherited attributes and its child nodes' synthesized attributes to the node's
-- synthesized attributes and the children nodes' inherited attributes.
type Rule t g =  forall sem . sem ~ Semantics t
              => (Inherited   t (g sem (Semantics t)), g sem (Synthesized t))
              -> (Synthesized t (g sem (Semantics t)), g sem (Inherited t))

-- | Transformation wrapper that keeps all the original tree nodes alongside their attributes
newtype Keep t (f :: Type -> Type) = Keep t
type instance Atts (Inherited (Keep t f)) g = Atts (Inherited t) g
type instance Atts (Synthesized (Keep t f)) g = (Atts (Inherited t) g, Atts (Synthesized t) g, f (g f f))

instance (Rank2.Functor (g (Semantics (Keep t s))), Functor s, Attribution t g s) => Attribution (Keep t s) g s where
   attribution (Keep t) x (Inherited i, childSynthesis) = (Synthesized synthesis', childInheritance') where
      (Synthesized s, childInheritance) = attribution t x (Inherited i :: Inherited t (g (Semantics t) (Semantics t)),
                                                           unsafeCoerce $ resynthesize Rank2.<$> childSynthesis)
      resynthesize :: forall a. Synthesized (Keep t s) a -> Synthesized t a
      resynthesize (Synthesized (_inherited, synthesized, _node)) = Synthesized synthesized
      synthesis' :: Atts (Synthesized (Keep t s)) g
      synthesis' = (i, s, (unsafeCoerce (localChild Rank2.<$> childSynthesis) :: g s s) <$ x)
      childInheritance' :: g (Semantics (Keep t s)) (Inherited (Keep t s))
      childInheritance' = unsafeCoerce childInheritance
      localChild :: Synthesized (Keep t s) a -> s a
      localChild (Synthesized (_, _, a)) = unsafeCoerce a

-- | The core function to tie the recursive knot, turning a 'Rule' for a node into its 'Semantics'.
knit :: (Rank2.Apply (g sem), sem ~ Semantics t) => Rule t g -> g sem sem -> sem (g sem sem)
knit r chSem = Rank2.Arrow knit'
   where knit' inherited = synthesized
            where (synthesized, chInh) = r (inherited, chSyn)
                  chSyn = chSem Rank2.<*> chInh

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
class Attribution t g shallow where
   -- | The attribution rule for a given transformation and node.
   attribution :: forall f. Rank2.Functor (g f) => t -> shallow (g f f) -> Rule t g

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Attribution t g p)
             => (forall a. p a -> a) -> t -> p x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}
