{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
             TypeFamilies, UndecidableInstances #-}

-- | A special case of an attribute grammar where every node has only a single inherited and a single synthesized
-- attribute of the same monoidal type. The synthesized attributes of child nodes are all 'mconcat`ted together.

module Transformation.AG.Monomorphic where

import Data.Functor.Const (Const(..))
import qualified Rank2
import Transformation (Domain, Codomain)
import qualified Transformation.Deep as Deep

data Atts a = Atts{
   inh :: a,
   syn :: a}

-- | A node's 'Semantics' maps its inherited attribute to its synthesized attribute.
type Semantics a = Const (a -> a)

-- | An attribution rule maps a node's inherited attribute and its child nodes' synthesized attribute to the node's
-- synthesized attribute and the children nodes' inherited attributes.
type Rule a =  Const (Atts a -> Atts a)

-- | The core function to tie the recursive knot, turning a 'Rule' for a node into its 'Semantics'.
knit :: (Rank2.Foldable (g sem), sem ~ Semantics a, Monoid a)
     => Rule a (g sem sem) -> g sem sem -> sem (g sem sem)
knit r chSem = Const knit'
   where knit' inherited = synthesized
            where Atts{syn= synthesized, inh= chInh} = getConst r Atts{inh= inherited, syn= chSyn}
                  chSyn = Rank2.foldMap (($ chInh) . getConst) chSem

-- | The core type class for defining the attribute grammar. The instances of this class typically have a form like
--
-- > instance Attribution MyAttGrammar MyMonoid MyNode (Semantics MyAttGrammar) Identity where
-- >   attribution MyAttGrammar{} (Identity MyNode{})
-- >               Atts{inh= fromParent,
-- >                    syn= fromChildren}
-- >             = Atts{syn= toParent,
-- >                    inh= toChildren}
class Attribution t a g deep shallow where
   -- | The attribution rule for a given transformation and node.
   attribution :: t -> shallow (g deep deep) -> Rule a (g (Semantics a) (Semantics a))

-- | Drop-in implementation of 'Transformation.$'
applyDefault :: (p ~ Domain t, q ~ Semantics a, x ~ g q q, Rank2.Foldable (g q), Attribution t a g q p, Monoid a)
             => (forall y. p y -> y) -> t -> p x -> q x
applyDefault extract t x = knit (attribution t x) (extract x)
{-# INLINE applyDefault #-}

-- | Drop-in implementation of 'Transformation.Full.<$>'
fullMapDefault :: (p ~ Domain t, q ~ Semantics a, q ~ Codomain t, x ~ g q q, Rank2.Foldable (g q),
                   Deep.Functor t g, Attribution t a g p p, Monoid a)
               => (forall y. p y -> y) -> t -> p (g p p) -> q (g q q)
fullMapDefault extract t local = knit (attribution t local) (t Deep.<$> extract local)
{-# INLINE fullMapDefault #-}
