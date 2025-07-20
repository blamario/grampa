{-# Language Haskell2010, DefaultSignatures, DeriveDataTypeable,
             FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | A special case of an attribute grammar where every node has only a single inherited and a single synthesized
-- attribute of the same monoidal type. The synthesized attributes of child nodes are all 'mconcat`ted together.

module Transformation.AG.Dimorphic where

import Data.Data (Data, Typeable)
import Data.Functor.Const (Const(..))
import Data.Kind (Type)
import Data.Semigroup (Semigroup(..))
import Unsafe.Coerce (unsafeCoerce)
import qualified Rank2
import Transformation (Transformation, Domain, Codomain, At)
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.AG as AG

-- | Transformation wrapper that allows automatic inference of attribute rules.
newtype Auto t = Auto t

-- | Node attributes
data Atts a b = Atts{
   -- | inherited
   inh :: a,
   -- | synthesized
   syn :: b}
   deriving (Data, Typeable, Show)

instance (Semigroup a, Semigroup b) => Semigroup (Atts a b) where
   Atts i1 s1 <> Atts i2 s2 = Atts (i1 <> i2) (s1 <> s2)

instance (Monoid a, Monoid b) => Monoid (Atts a b) where
   mappend = (<>)
   mempty = Atts mempty mempty

-- | A node's 'Semantics' maps its inherited attribute to its synthesized attribute.
type Semantics a b = Const (a -> b)

-- | An attribution rule maps a node's inherited attribute and its child nodes' synthesized attributes to the node's
-- synthesized attribute and the children nodes' inherited attributes.
type Rule a b = Atts a b -> Atts a b

instance {-# overlappable #-} AttributeTransformation t => Attribution t g where
   attribution = const (const id)

instance {-# overlappable #-} (Transformation (Auto t), p ~ Domain (Auto t), q ~ Codomain (Auto t), q ~ Semantics a b,
                               a ~ Inherited (Auto t), b ~ Synthesized (Auto t),
                               Rank2.Foldable (g q), Rank2.Functor (g q),
                               Monoid a, Monoid b, Foldable p, Attribution (Auto t) g) =>
                              (Auto t) `At` g (Semantics a b) (Semantics a b) where
   ($) = applyDefault (foldr const $ error "Missing node")
   {-# INLINE ($) #-}

instance (Transformation (Auto t), Domain (Auto t) ~ f, Functor f, Codomain (Auto t) ~ Semantics a b,
          Rank2.Functor (g f), Deep.Functor (Auto t) g, Auto t `At` g (Semantics a b) (Semantics a b)) =>
         Full.Functor (Auto t) g where
   (<$>) = Full.mapUpDefault

-- | The core function to tie the recursive knot, turning a 'Rule' for a node into its 'Semantics'.
knit :: (Rank2.Foldable (g sem), sem ~ Semantics a b, Monoid a, Monoid b)
     => Rule a b -> g sem sem -> sem (g sem sem)
knit r chSem = Const knitted
   where knitted inherited = synthesized
            where Atts{syn= synthesized, inh= chInh} = r Atts{inh= inherited, syn= chSyn}
                  chSyn = Rank2.foldMap (($ chInh) . getConst) chSem

-- | Class of transformations that assign the same type of inherited and synthesized attributes to every node.
class Transformation t => AttributeTransformation t where
   type Inherited t :: Type
   type Synthesized t :: Type

type instance AG.Atts (AG.Inherited (Auto t)) g = Inherited (Auto t)
type instance AG.Atts (AG.Synthesized (Auto t)) g = Synthesized (Auto t)

instance (Foldable f, Attribution (Auto t) g,
          Rank2.Foldable (g (AG.Semantics (Auto t))), Rank2.Functor (g (AG.Semantics (Auto t))),
          Monoid (Synthesized (Auto t)), f ~ Domain (Auto t)) => AG.Attribution (Auto t) g f where
   attribution t x (inherited, chSyn) = (AG.Synthesized $ unsafeCoerce $ syn result, unsafeCoerce chInh)
      where result = attribution t x Atts{inh=AG.inh inherited, syn=Rank2.foldMap AG.syn chSyn}
            chInh = uniformInheritance Rank2.<$> foldr const (error "Missing node") x
            uniformInheritance :: forall p a. p a -> AG.Inherited (Auto t) a
            uniformInheritance = const $ AG.Inherited (AG.inh inherited)

-- | The core type class for defining the attribute grammar. The instances of this class typically have a form like
--
-- > instance Attribution MyAttGrammar MyMonoid MyNode (Semantics MyAttGrammar) Identity where
-- >   attribution MyAttGrammar{} (Identity MyNode{})
-- >               Atts{inh= fromParent,
-- >                    syn= fromChildren}
-- >             = Atts{syn= toParent,
-- >                    inh= toChildren}
class AttributeTransformation t => Attribution t (g :: (Type -> Type) -> (Type -> Type) -> Type) where
   -- | The attribution rule for a given transformation and node.
   attribution :: forall f. Rank2.Functor (g f) => t -> Domain t (g f f) -> Rule (Inherited t) (Synthesized t)

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (p ~ Domain t, q ~ Codomain t, a ~ Inherited t, b ~ Synthesized t, q ~ Semantics a b, x ~ g q q,
                 Rank2.Foldable (g q), Rank2.Functor (g q), Attribution t g, Monoid a, Monoid b)
             => (forall y. p y -> y) -> t -> p x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Full.<$>'
fullMapDefault :: (p ~ Domain t, a ~ Inherited t, b ~ Synthesized t, q ~ Semantics a b, q ~ Codomain t, x ~ g q q,
                   Functor p, Rank2.Functor (g q), Rank2.Foldable (g q), Deep.Functor t g, Attribution t g,
                   Monoid a, Monoid b)
               => (forall y. p y -> y) -> t -> p (g p p) -> q (g q q)
fullMapDefault extract t x = knit (attribution t (y <$ x)) y
   where y = t Deep.<$> extract x
{-# INLINE fullMapDefault #-}
