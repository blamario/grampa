{-# Language FlexibleContexts, FlexibleInstances, KindSignatures, MultiParamTypeClasses, PatternSynonyms, RankNTypes,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | A special case of an attribute grammar where every node has only a single inherited and a single synthesized
-- attribute of the same monoidal type. The synthesized attributes of child nodes are all 'mconcat`ted together.

module Transformation.AG.Monomorphic (
  Auto (Auto), Keep (Keep), Atts, pattern Atts, inh, syn,
  Semantics, Rule, Attribution (attribution),
  Dimorphic.knit, applyDefault, fullMapDefault) where

import Data.Functor.Const (Const(..))
import Data.Kind (Type)
import qualified Rank2
import Transformation (Transformation, Domain, Codomain, At)
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

import qualified Transformation.AG.Dimorphic as Dimorphic
import Transformation.AG.Dimorphic (knit)


-- | Transformation wrapper that allows automatic inference of attribute rules.
newtype Auto t = Auto t

-- | Transformation wrapper that allows automatic inference of attribute rules and preservation of the attribute with
-- the original nodes.
newtype Keep t = Keep t

type Atts a = Dimorphic.Atts a a

pattern Atts :: a -> a -> Atts a
pattern Atts{inh, syn} = Dimorphic.Atts inh syn

-- | A node's 'Semantics' maps its inherited attribute to its synthesized attribute.
type Semantics a = Const (a -> a)

-- | An attribution rule maps a node's inherited attribute and its child nodes' synthesized attribute to the node's
-- synthesized attribute and the children nodes' inherited attributes.
type Rule a = Atts a -> Atts a

instance {-# overlappable #-} AttributeTransformation t => Attribution t g where
   attribution = const (const id)

instance {-# overlappable #-} (Transformation (Auto t), p ~ Domain (Auto t), q ~ Codomain (Auto t), q ~ Semantics a,
                               a ~ Attributes (Auto t),
                               Rank2.Foldable (g q), Monoid a, Foldable p, Attribution (Auto t) g) =>
                              (Auto t) `At` g (Semantics a) (Semantics a) where
   ($) = applyDefault (foldr const $ error "Missing node")
   {-# INLINE ($) #-}

instance (Transformation (Auto t), Domain (Auto t) ~ f, Functor f, Codomain (Auto t) ~ Semantics a,
          Rank2.Functor (g f), Deep.Functor (Auto t) g, Auto t `At` g (Semantics a) (Semantics a)) =>
         Full.Functor (Auto t) g where
   (<$>) = Full.mapUpDefault

-- | Class of transformations that assign the same type of attributes to every node.
class Transformation t => AttributeTransformation t where
   type Attributes t :: Type

-- | The core type class for defining the attribute grammar. The instances of this class typically have a form like
--
-- > instance Attribution MyAttGrammar MyMonoid MyNode (Semantics MyAttGrammar) Identity where
-- >   attribution MyAttGrammar{} (Identity MyNode{})
-- >               Atts{inh= fromParent,
-- >                    syn= fromChildren}
-- >             = Atts{syn= toParent,
-- >                    inh= toChildren}
class AttributeTransformation t => Attribution t g where
   -- | The attribution rule for a given transformation and node.
   attribution :: t -> Domain t (g (Codomain t) (Codomain t)) -> Rule (Attributes t)

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (a ~ Attributes t, q ~ Codomain t, q ~ Semantics a, x ~ g q q, Rank2.Foldable (g q), Attribution t g,
                 Monoid a)
             => (forall y. Domain t y -> y) -> t -> Domain t x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Full.<$>'
fullMapDefault :: (p ~ Domain t, q ~ Semantics a, a ~ Attributes t, q ~ Codomain t, x ~ g q q, Rank2.Foldable (g q),
                   Functor p, Deep.Functor t g, Attribution t g, Monoid a)
               => (forall y. p y -> y) -> t -> p (g p p) -> q (g q q)
fullMapDefault extract t x = knit (attribution t (y <$ x)) y
   where y = t Deep.<$> extract x
{-# INLINE fullMapDefault #-}
