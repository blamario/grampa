{-# Language DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}

-- | A special case of an attribute grammar where every node has only a single inherited and a single synthesized
-- attribute of the same monoidal type. The synthesized attributes of child nodes are all 'mconcat`ted together.

module Transformation.AG.Monomorphic where

import Data.Data (Data, Typeable)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Kind (Type)
import qualified Rank2
import Transformation (Transformation, Domain, Codomain)
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

data Atts a = Atts{
   inh :: a,
   syn :: a}
   deriving (Data, Typeable, Show)

instance Semigroup a => Semigroup (Atts a) where
   Atts i1 s1 <> Atts i2 s2 = Atts (i1 <> i2) (s1 <> s2)

instance Monoid a => Monoid (Atts a) where
   mempty = Atts mempty mempty

-- | A node's 'Semantics' maps its inherited attribute to its synthesized attribute.
type Semantics a = Const (a -> a)

-- | An attribution rule maps a node's inherited attribute and its child nodes' synthesized attribute to the node's
-- synthesized attribute and the children nodes' inherited attributes.
type Rule a = Atts a -> Atts a

-- | The core function to tie the recursive knot, turning a 'Rule' for a node into its 'Semantics'.
knit :: (Rank2.Foldable (g sem), sem ~ Semantics a, Monoid a)
     => Rule a -> g sem sem -> sem (g sem sem)
knit r chSem = Const knitted
   where knitted inherited = synthesized
            where Atts{syn= synthesized, inh= chInh} = r Atts{inh= inherited, syn= chSyn}
                  chSyn = Rank2.foldMap (($ chInh) . getConst) chSem

instance {-# OVERLAPPABLE #-} Attribution t a g deep shallow where
   attribution = const (const id)

-- | Another way to tie the recursive knot, using a 'Rule' to add attributes to every node througha stateful calculation
knitKeeping :: forall a f g sem. (Rank2.Foldable (g sem), sem ~ Compose ((,) (Atts a)) f, Monoid a, Foldable f, Functor f)
            => Rule a -> f (g sem sem) -> Compose (State a) (Compose ((,) (Atts a)) f) (g sem sem)
knitKeeping r x = Compose (state knitted)
   where knitted :: a -> (Compose ((,) (Atts a)) f (g sem sem), a)
         knitted inherited = (Compose (results{inh= inherited}, x), chInh)
            where results@Atts{inh= chInh} = r Atts{inh= inherited, syn= chSyn}
                  chSyn = foldMap (Rank2.foldMap (syn . fst . getCompose)) x
                                        
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
applyDefault :: (p ~ Domain t, q ~ Semantics a, x ~ g q q, Rank2.Foldable (g q), Attribution t a g q p,
                 Monoid a)
             => (forall y. p y -> y) -> t -> p x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Transformation.Full.<$>'
fullMapDefault :: (p ~ Domain t, q ~ Semantics a, q ~ Codomain t, x ~ g q q, Rank2.Foldable (g q),
                   Deep.Functor t g, Attribution t a g p p, Monoid a)
               => (forall y. p y -> y) -> t -> p (g p p) -> q (g q q)
fullMapDefault extract t local = knit (attribution t local) (t Deep.<$> extract local)
{-# INLINE fullMapDefault #-}

-- | Drop-in implementation of 'Transformation.Full.<$>' that stores all attributes with every original node
applyDefaultWithAttributes :: (p ~ Domain t, q ~ Compose ((,) (Atts a)) p, x ~ g q q,
                               Attribution t a g q p, Rank2.Foldable (g q), Monoid a, Foldable p, Functor p)
                           => t -> p x -> Compose (State a) q x
applyDefaultWithAttributes t x = knitKeeping (attribution t x) x
{-# INLINE applyDefaultWithAttributes #-}

-- | Drop-in implementation of 'Transformation.Full.<$>' that stores all attributes with every original node
fullMapDefaultWithAttributes :: (Transformation t, Domain t ~ p, Codomain t ~ Compose (State a) q, Full.Traversable t g,
                                 q ~ Compose ((,) (Atts a)) f)
                             => t -> a -> p (g p p) -> q (g q q)
fullMapDefaultWithAttributes t rootInheritance x = evalState (Full.traverse t x) rootInheritance
{-# INLINE fullMapDefaultWithAttributes #-}
