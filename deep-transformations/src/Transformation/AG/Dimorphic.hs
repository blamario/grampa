{-# Language DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | A special case of an attribute grammar where every node has only a single inherited and a single synthesized
-- attribute of the same monoidal type. The synthesized attributes of child nodes are all 'mconcat`ted together.

module Transformation.AG.Dimorphic where

import Data.Data (Data, Typeable)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Kind (Type)
import Data.Semigroup (Semigroup(..))
import qualified Rank2
import Transformation (Transformation, Domain, Codomain, At)
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

-- | Transformation wrapper that allows automatic inference of attribute rules.
newtype Auto t = Auto t

-- | Transformation wrapper that allows automatic inference of attribute rules and preservation of the attribute with
-- the original nodes.
newtype Keep t = Keep t

data Atts a b = Atts{
   inh :: a,
   syn :: b}
   deriving (Data, Typeable, Show)

instance (Semigroup a, Semigroup b) => Semigroup (Atts a b) where
   Atts i1 s1 <> Atts i2 s2 = Atts (i1 <> i2) (s1 <> s2)

instance (Monoid a, Monoid b) => Monoid (Atts a b) where
   mappend = (<>)
   mempty = Atts mempty mempty

-- | A node's 'Semantics' maps its inherited attribute to its synthesized attribute.
type Semantics a b = Const (a -> b)

-- | A node's 'PreservingSemantics' maps its inherited attribute to its synthesized attribute.
type PreservingSemantics f a b = Compose ((->) a) (Compose ((,) (Atts a b)) f)

-- | An attribution rule maps a node's inherited attribute and its child nodes' synthesized attribute to the node's
-- synthesized attribute and the children nodes' inherited attributes.
type Rule a b = Atts a b -> Atts a b

instance {-# overlappable #-} Attribution t a b g deep shallow where
   attribution = const (const id)

instance {-# overlappable #-} (Transformation (Auto t), p ~ Domain (Auto t), q ~ Codomain (Auto t), q ~ Semantics a b,
                               Rank2.Foldable (g q), Monoid a, Monoid b, Foldable p, Attribution (Auto t) a b g q p) =>
                              (Auto t) `At` g (Semantics a b) (Semantics a b) where
   ($) = applyDefault (foldr const $ error "Missing node")
   {-# INLINE ($) #-}

instance {-# overlappable #-} (Transformation (Keep t), p ~ Domain (Keep t), q ~ Codomain (Keep t),
                               q ~ PreservingSemantics p a b, Rank2.Foldable (g q), Monoid a, Monoid b,
                               Foldable p, Functor p, Attribution (Keep t) a b g q p) =>
                              (Keep t) `At` g (PreservingSemantics p a b) (PreservingSemantics p a b) where
   ($) = applyDefaultWithAttributes
   {-# INLINE ($) #-}

instance (Transformation (Auto t), Domain (Auto t) ~ f, Functor f, Codomain (Auto t) ~ Semantics a b,
          Rank2.Functor (g f), Deep.Functor (Auto t) g, Auto t `At` g (Semantics a b) (Semantics a b)) =>
         Full.Functor (Auto t) g where
   (<$>) = Full.mapUpDefault

instance (Transformation (Keep t), Domain (Keep t) ~ f, Functor f, Codomain (Keep t) ~ PreservingSemantics f a b,
          Rank2.Functor (g f), Deep.Functor (Keep t) g,
          Keep t `At` g (PreservingSemantics f a b) (PreservingSemantics f a b)) =>
         Full.Functor (Keep t) g where
   (<$>) = Full.mapUpDefault

instance (Transformation (Keep t), Domain (Keep t) ~ f, Traversable f, Rank2.Traversable (g f),
          Codomain (Keep t) ~ PreservingSemantics f a b, Deep.Traversable (Feeder a b f) g, Full.Functor (Keep t) g,
          Keep t `At` g (PreservingSemantics f a b) (PreservingSemantics f a b)) =>
         Full.Traversable (Keep t) g where
   traverse = traverseDefaultWithAttributes

-- | The core function to tie the recursive knot, turning a 'Rule' for a node into its 'Semantics'.
knit :: (Rank2.Foldable (g sem), sem ~ Semantics a b, Monoid a, Monoid b)
     => Rule a b -> g sem sem -> sem (g sem sem)
knit r chSem = Const knitted
   where knitted inherited = synthesized
            where Atts{syn= synthesized, inh= chInh} = r Atts{inh= inherited, syn= chSyn}
                  chSyn = Rank2.foldMap (($ chInh) . getConst) chSem

-- | Another way to tie the recursive knot, using a 'Rule' to add attributes to every node througha stateful calculation
knitKeeping :: forall a b f g sem. (Rank2.Foldable (g sem), sem ~ PreservingSemantics f a b,
                                    Monoid a, Monoid b, Foldable f, Functor f)
            => Rule a b -> f (g sem sem) -> sem (g sem sem)
knitKeeping r x = Compose knitted
   where knitted :: a -> Compose ((,) (Atts a b)) f (g sem sem)
         knitted inherited = Compose (results, x)
            where results@Atts{inh= chInh} = r Atts{inh= inherited, syn= chSyn}
                  chSyn = foldMap (Rank2.foldMap (syn . fst . getCompose . ($ chInh) . getCompose)) x

-- | The core type class for defining the attribute grammar. The instances of this class typically have a form like
--
-- > instance Attribution MyAttGrammar MyMonoid MyNode (Semantics MyAttGrammar) Identity where
-- >   attribution MyAttGrammar{} (Identity MyNode{})
-- >               Atts{inh= fromParent,
-- >                    syn= fromChildren}
-- >             = Atts{syn= toParent,
-- >                    inh= toChildren}
class Attribution t a b g (deep :: Type -> Type) shallow where
   -- | The attribution rule for a given transformation and node.
   attribution :: t -> shallow (g deep deep) -> Rule a b

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (p ~ Domain t, q ~ Semantics a b, x ~ g q q,
                 Rank2.Foldable (g q), Attribution t a b g q p, Monoid a, Monoid b)
             => (forall y. p y -> y) -> t -> p x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Full.<$>'
fullMapDefault :: (p ~ Domain t, q ~ Semantics a b, q ~ Codomain t, x ~ g q q, Rank2.Foldable (g q),
                   Deep.Functor t g, Attribution t a b g p p, Monoid a, Monoid b)
               => (forall y. p y -> y) -> t -> p (g p p) -> q (g q q)
fullMapDefault extract t local = knit (attribution t local) (t Deep.<$> extract local)
{-# INLINE fullMapDefault #-}

-- | Drop-in implementation of 'Transformation.$' that stores all attributes with every original node
applyDefaultWithAttributes :: (p ~ Domain t, q ~ PreservingSemantics p a b, x ~ g q q,
                               Attribution t a b g q p, Rank2.Foldable (g q), Monoid a, Monoid b, Foldable p, Functor p)
                           => t -> p x -> q x
applyDefaultWithAttributes t x = knitKeeping (attribution t x) x
{-# INLINE applyDefaultWithAttributes #-}

-- | Drop-in implementation of 'Full.traverse' that stores all attributes with every original node
traverseDefaultWithAttributes :: forall t p q r a b g.
                                 (Transformation t, Domain t ~ p, Codomain t ~ Compose ((->) a) q,
                                 q ~ Compose ((,) (Atts a b)) p, r ~ Compose ((->) a) q,
                                 Traversable p, Full.Functor t g, Deep.Traversable (Feeder a b p) g,
                                 Transformation.At t (g r r))
                              => t -> p (g p p) -> a -> q (g q q)
traverseDefaultWithAttributes t x rootInheritance = Full.traverse Feeder (t Full.<$> x) rootInheritance
{-# INLINE traverseDefaultWithAttributes #-}

data Feeder a b (f :: Type -> Type) = Feeder

type FeederDomain a b f = Compose ((->) a) (Compose ((,) (Atts a b)) f)

instance Transformation (Feeder a b f) where
   type Domain (Feeder a b f) = FeederDomain a b f
   type Codomain (Feeder a b f) = FeederDomain a b f

instance Transformation.At (Feeder a b f) g where
   Feeder $ x = x

instance (Traversable f, Rank2.Traversable (g (FeederDomain a b f)), Deep.Traversable (Feeder a b f) g) =>
         Full.Traversable (Feeder a b f) g where
   traverse t x inheritance = Compose (atts{inh= inheritance}, traverse (Deep.traverse t) y (inh atts))
      where Compose (atts, y) = getCompose x inheritance
