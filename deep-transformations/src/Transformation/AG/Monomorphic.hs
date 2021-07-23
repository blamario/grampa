{-# Language DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | A special case of an attribute grammar where every node has only a single inherited and a single synthesized
-- attribute of the same monoidal type. The synthesized attributes of child nodes are all 'mconcat`ted together.

module Transformation.AG.Monomorphic where

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

data Atts a = Atts{
   inh :: a,
   syn :: a}
   deriving (Data, Typeable, Show)

instance Semigroup a => Semigroup (Atts a) where
   Atts i1 s1 <> Atts i2 s2 = Atts (i1 <> i2) (s1 <> s2)

instance Monoid a => Monoid (Atts a) where
   mappend = (<>)
   mempty = Atts mempty mempty

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

instance (Transformation (Auto t), Domain (Auto t) ~ f, Functor f, Codomain (Auto t) ~ Semantics (Auto t),
          Deep.Functor (Auto t) g, Auto t `At` g (Semantics (Auto t)) (Semantics (Auto t))) =>
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
   traverse = traverseDefaultWithAttributes

-- | The core function to tie the recursive knot, turning a 'Rule' for a node into its 'Semantics'.
knit :: (Rank2.Foldable (g sem), sem ~ Semantics a, Monoid a)
     => Rule a -> g sem sem -> sem (g sem sem)
knit r chSem = Const knitted
   where knitted inherited = synthesized
            where Atts{syn= synthesized, inh= chInh} = r Atts{inh= inherited, syn= chSyn}
                  chSyn = Rank2.foldMap (($ chInh) . getConst) chSem

-- | Another way to tie the recursive knot, using a 'Rule' to add attributes to every node througha stateful calculation
knitKeeping :: forall a f g sem. (Rank2.Foldable (g sem), sem ~ PreservingSemantics f a,
                              Monoid a, Foldable f, Functor f)
            => Rule a -> f (g sem sem) -> sem (g sem sem)
knitKeeping r x = Compose knitted
   where knitted :: a -> Compose ((,) (Atts a)) f (g sem sem)
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

-- | Drop-in implementation of 'Full.traverse' that stores all attributes with every original node
traverseDefaultWithAttributes :: forall t p q r a g.
                                 (Transformation t, Domain t ~ p, Codomain t ~ Compose ((->) a) q,
                                 q ~ Compose ((,) (Atts a)) p, r ~ Compose ((->) a) q,
                                 Traversable p, Full.Functor t g, Deep.Traversable (Feeder a p) g,
                                 Transformation.At t (g r r))
                              => t -> p (g p p) -> a -> q (g q q)
traverseDefaultWithAttributes t x rootInheritance = Full.traverse Feeder (t Full.<$> x) rootInheritance
{-# INLINE traverseDefaultWithAttributes #-}

data Feeder a (f :: Type -> Type) = Feeder

instance Transformation (Feeder a f) where
   type Domain (Feeder a f) = Compose ((->) a) (Compose ((,) (Atts a)) f)
   type Codomain (Feeder a f) = Compose ((->) a) (Compose ((,) (Atts a)) f)

instance Transformation.At (Feeder a f) g where
   Feeder $ x = x

instance (Traversable f, Deep.Traversable (Feeder a f) g) => Full.Traversable (Feeder a f) g where
   traverse t x inheritance = Compose (atts{inh= inheritance}, traverse (Deep.traverse t) y (inh atts))
      where Compose (atts, y) = getCompose x inheritance
