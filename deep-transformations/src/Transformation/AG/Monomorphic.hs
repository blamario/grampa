{-# Language FlexibleContexts, FlexibleInstances, KindSignatures, MultiParamTypeClasses, PatternSynonyms, RankNTypes,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | A special case of an attribute grammar where every node has only a single inherited and a single synthesized
-- attribute of the same monoidal type. The synthesized attributes of child nodes are all 'mconcat`ted together.

module Transformation.AG.Monomorphic (
  Auto (Auto), Keep (Keep), Atts, pattern Atts, inh, syn,
  Semantics, PreservingSemantics, Rule, Attribution (attribution), Feeder,
  Dimorphic.knit, Dimorphic.knitKeeping,
  applyDefault, applyDefaultWithAttributes,
  fullMapDefault, Dimorphic.traverseDefaultWithAttributes) where

import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Kind (Type)
import qualified Rank2
import Transformation (Transformation, Domain, Codomain, At)
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

import qualified Transformation.AG.Dimorphic as Dimorphic
import Transformation.AG.Dimorphic (knit, knitKeeping)


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

-- | A node's 'PreservingSemantics' maps its inherited attribute to its synthesized attribute.
type PreservingSemantics f a = Compose ((->) a) (Compose ((,) (Atts a)) f)

-- | An attribution rule maps a node's inherited attribute and its child nodes' synthesized attribute to the node's
-- synthesized attribute and the children nodes' inherited attributes.
type Rule a = Atts a -> Atts a

instance {-# overlappable #-} Attribution t a g deep shallow where
   attribution = const (const id)

instance {-# overlappable #-} (Transformation (Auto t), p ~ Domain (Auto t), q ~ Codomain (Auto t), q ~ Semantics a,
                               Rank2.Foldable (g q), Monoid a, Foldable p, Attribution (Auto t) a g q p) =>
                              (Auto t) `At` g (Semantics a) (Semantics a) where
   ($) = applyDefault (foldr const $ error "Missing node")
   {-# INLINE ($) #-}

instance {-# overlappable #-} (Transformation (Keep t), p ~ Domain (Keep t), q ~ Codomain (Keep t),
                               q ~ PreservingSemantics p a, Rank2.Foldable (g q), Monoid a,
                               Foldable p, Functor p, Attribution (Keep t) a g q p) =>
                              (Keep t) `At` g (PreservingSemantics p a) (PreservingSemantics p a) where
   ($) = applyDefaultWithAttributes
   {-# INLINE ($) #-}

instance (Transformation (Auto t), Domain (Auto t) ~ f, Functor f, Codomain (Auto t) ~ Semantics a,
          Deep.Functor (Auto t) g, Auto t `At` g (Semantics a) (Semantics a)) =>
         Full.Functor (Auto t) g where
   (<$>) = Full.mapUpDefault

instance (Transformation (Keep t), Domain (Keep t) ~ f, Functor f, Codomain (Keep t) ~ PreservingSemantics f a,
          Functor f, Deep.Functor (Keep t) g,
          Keep t `At` g (PreservingSemantics f a) (PreservingSemantics f a)) =>
         Full.Functor (Keep t) g where
   (<$>) = Full.mapUpDefault

instance (Transformation (Keep t), Domain (Keep t) ~ f, Traversable f, Rank2.Traversable (g f),
          Codomain (Keep t) ~ PreservingSemantics f a, Deep.Traversable (Feeder a f) g, Full.Functor (Keep t) g,
          Keep t `At` g (PreservingSemantics f a) (PreservingSemantics f a)) =>
         Full.Traversable (Keep t) g where
   traverse = Dimorphic.traverseDefaultWithAttributes

-- | The core type class for defining the attribute grammar. The instances of this class typically have a form like
--
-- > instance Attribution MyAttGrammar MyMonoid MyNode (Semantics MyAttGrammar) Identity where
-- >   attribution MyAttGrammar{} (Identity MyNode{})
-- >               Atts{inh= fromParent,
-- >                    syn= fromChildren}
-- >             = Atts{syn= toParent,
-- >                    inh= toChildren}
class Attribution t a g (deep :: Type -> Type) shallow where
   -- | The attribution rule for a given transformation and node.
   attribution :: t -> shallow (g deep deep) -> Rule a

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (p ~ Domain t, q ~ Semantics a, x ~ g q q, Rank2.Foldable (g q), Attribution t a g q p, Monoid a)
             => (forall y. p y -> y) -> t -> p x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Full.<$>'
fullMapDefault :: (p ~ Domain t, q ~ Semantics a, q ~ Codomain t, x ~ g q q, Rank2.Foldable (g q),
                   Deep.Functor t g, Attribution t a g p p, Monoid a)
               => (forall y. p y -> y) -> t -> p (g p p) -> q (g q q)
fullMapDefault extract t local = knit (attribution t local) (t Deep.<$> extract local)
{-# INLINE fullMapDefault #-}

-- | Drop-in implementation of 'Transformation.$' that stores all attributes with every original node
applyDefaultWithAttributes :: (p ~ Domain t, q ~ PreservingSemantics p a, x ~ g q q,
                               Attribution t a g q p, Rank2.Foldable (g q), Monoid a, Foldable p, Functor p)
                           => t -> p x -> q x
applyDefaultWithAttributes t x = knitKeeping (attribution t x) x
{-# INLINE applyDefaultWithAttributes #-}

type Feeder a = Dimorphic.Feeder a a
