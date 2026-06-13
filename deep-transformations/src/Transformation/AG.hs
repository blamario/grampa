{-# Language FlexibleContexts, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving, ImpredicativeTypes,
             MultiParamTypeClasses, NamedFieldPuns, QuantifiedConstraints,
             RankNTypes, ScopedTypeVariables, StandaloneDeriving,
             TypeApplications, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | An attribute grammar is a particular kind of 'Transformation' that assigns attributes to nodes in a
-- tree. Different node types may have different types of attributes, so the transformation is not natural. All
-- attributes are divided into 'Inherited' and 'Synthesized' attributes.

module Transformation.AG where

import Data.Foldable1 as Foldable1
import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)

import qualified Rank2
import Transformation (Transformation, Codomain)
import Transformation.Deep (Const2)
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

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
class Attribution t where
   type Origin t :: Type -> Type

class Attribution t => At t g where
   -- | The attribution rule for a given transformation and node.
   attribution :: forall sem. Rank2.Traversable (g sem)
               => t -> Origin t (g sem sem)
               -> (Inherited   t (g sem sem), g sem (Synthesized t))
               -> (Synthesized t (g sem sem), g sem (Inherited t))

-- | Turns an `Attribution` into a `Transformation`
newtype Knit t = Knit t

instance Attribution t => Transformation (Knit t) where
   type Domain (Knit t) = Origin t
   type Codomain (Knit t) = Semantics t

instance (t `At` g, Rank2.Apply (g sem), Rank2.Traversable (g sem), sem ~ Semantics t, Foldable1 (Origin t)) =>
         Knit t `Transformation.At` g sem sem where
   Knit t $ x = knit (attribution t x) (Foldable1.head x)

instance (t `At` g, Rank2.Apply (g (Semantics t)), Rank2.Traversable (g (Semantics t)),
          Foldable1 (Origin t), Functor (Origin t), Rank2.Functor (g (Origin t)), Deep.Functor (Knit t) g) =>
         Full.Functor (Knit t) g where
   (<$>) = Full.mapUpDefault

instance (Attribution t1, Attribution t2, Origin t1 ~ Origin t2) => Attribution (t1, t2) where
  type Origin (t1, t2) = Origin t1

type instance Atts (Inherited (t1, t2)) g = (Atts (Inherited t1) g, Atts (Inherited t2) g)
type instance Atts (Synthesized (t1, t2)) g = (Atts (Synthesized t1) g, Atts (Synthesized t2) g)

instance {-# OVERLAPPABLE #-} (t1 `At` g, t2 `At` g, Origin t1 ~ Origin t2, forall sem. Rank2.Apply (g sem)) =>
  (t1, t2) `At` g where
  attribution (t1, t2) x (Inherited (i1, i2), s) = (Synthesized (s1, s2), Rank2.liftA2 pairInh i1' i2')
    where (Synthesized s1, i1') = attribution t1 x (Inherited i1, Synthesized . fst . syn Rank2.<$> s)
          (Synthesized s2, i2') = attribution t2 x (Inherited i2, Synthesized . snd . syn Rank2.<$> s)
          pairInh (Inherited inh1) (Inherited inh2) = Inherited (inh1, inh2)

-- | Attribution wrapper that keeps all the original tree nodes alongside their attributes in a `Kept` node
newtype Keep t = Keep t deriving (Attribution)

-- | The synthesized attributes of a `Keep`-wrapped attribution
data Kept t a = Kept{inherited   :: Atts (Inherited t) (NodeConstructor a),
                     synthesized :: Atts (Synthesized t) (NodeConstructor a),
                     original    :: Origin t a}

deriving instance (Show (Atts (Inherited t) (NodeConstructor a)),
                   Show (Atts (Synthesized t) (NodeConstructor a)),
                   Show (Origin t a)) => Show (Kept t a)

type instance Atts (Inherited (Keep t)) g = Atts (Inherited t) g
type instance Atts (Synthesized (Keep t)) g = Kept t (g (Kept t) (Kept t))

instance (Rank2.Functor (g (Semantics (Keep t))), Functor (Origin t), t `At` g) => Keep t `At` g where
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
