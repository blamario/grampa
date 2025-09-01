{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, NamedFieldPuns, RankNTypes, StandaloneDeriving,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | The RepMin example using 'AG.Keep' to replicate the tree structure.
module RepMinKeep where

import Data.Functor.Identity
import Data.Kind (Type)
import qualified Rank2
import Transformation (Transformation(..))
import Transformation.AG (Inherited(..), Synthesized(..))
import qualified Transformation
import qualified Transformation.AG as AG
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

-- | tree data type
data Tree a (f' :: Type -> Type) (f :: Type -> Type) = Fork{left :: f (Tree a f' f'),
                                                            right:: f (Tree a f' f')}
                                                     | Leaf{leafValue :: f a}
-- | tree root
data Root a f' f = Root{root :: f (Tree a f' f')}

deriving instance (Show (f (Tree a f' f')), Show (f a)) => Show (Tree a f' f)
deriving instance (Show (f (Tree a f' f'))) => Show (Root a f' f)

instance Rank2.Functor (Tree a f') where
   f <$> Fork l r = Fork (f l) (f r)
   f <$> Leaf x = Leaf (f x)

instance Rank2.Functor (Root a f') where
   f <$> Root x = Root (f x)

instance Rank2.Foldable (Tree a f') where
   f `foldMap` Fork l r = f l <> f r
   f `foldMap` Leaf x = f x

instance Rank2.Traversable (Root a f') where
   f `traverse` Root x = Root <$> f x

instance Rank2.Traversable (Tree a f') where
   f `traverse` Fork l r = Fork <$> f l <*> f r
   f `traverse` Leaf x = Leaf <$> f x

instance Rank2.Foldable (Root a f') where
   f `foldMap` Root x = f x

instance Rank2.Apply (Tree a f') where
   Fork fl fr <*> ~(Fork l r) = Fork (Rank2.apply fl l) (Rank2.apply fr r)
   Leaf f <*> ~(Leaf x) = Leaf (Rank2.apply f x)

instance Rank2.Applicative (Tree a f') where
   pure x = Leaf x

instance Rank2.Apply (Root a f') where
   Root f <*> ~(Root x) = Root (Rank2.apply f x)

instance (Transformation t, Transformation.At t a, Full.Functor t (Tree a)) => Deep.Functor t (Tree a) where
   t <$> Fork l r = Fork (t Full.<$> l) (t Full.<$> r)
   t <$> Leaf x = Leaf (t Transformation.$ x)

instance (Transformation t, Full.Functor t (Tree a)) => Deep.Functor t (Root a) where
   t <$> Root x = Root (t Full.<$> x)

-- | The transformation type
data RepMin = RepMin

type Sem = AG.PreservingSemantics RepMin

instance Transformation RepMin where
   type Domain RepMin = Identity
   type Codomain RepMin = Sem

-- | Inherited attributes' type
data InhRepMin = InhRepMin{global :: Int} deriving Show

-- | Synthesized attributes' type
data SynRepMin = SynRepMin{local :: Int} deriving Show

type instance AG.Atts (Inherited RepMin) (Tree Int) = InhRepMin
type instance AG.Atts (Synthesized RepMin) (Tree Int) = SynRepMin
type instance AG.Atts (Inherited RepMin) (Root Int) = ()
type instance AG.Atts (Synthesized RepMin) (Root Int) = SynRepMin

type instance AG.Atts (Inherited RepMin) (Deep.Const2 Int) = InhRepMin
type instance AG.Atts (Synthesized RepMin) (Deep.Const2 Int) = Int

instance Transformation.At RepMin (Tree Int Sem Sem) where
  ($) = AG.applyDefaultWithAttributes runIdentity
instance Transformation.At RepMin (Root Int Sem Sem) where
  RepMin $ root = AG.applyDefaultWithAttributes runIdentity RepMin root

instance Full.Functor RepMin (Tree Int) where
  (<$>) = Full.mapUpDefault
instance Full.Functor RepMin (Root Int) where
  (<$>) = Full.mapUpDefault

-- | The semantics of the primitive 'Int' type must be defined manually.
instance Transformation.At RepMin Int where
   RepMin $ Identity n = Rank2.Arrow (\(Inherited i)-> AG.Kept i n (Identity $ Deep.Const2 n))

instance AG.Attribution RepMin (Root Int) where
   attribution RepMin self (inherited, Root root) = (Synthesized SynRepMin{local= local (syn root)},
                                                     Root{root= Inherited InhRepMin{global= local (syn root)}})

instance AG.Attribution RepMin (Tree Int) where
   attribution _ _ (inherited, Fork left right) = (Synthesized SynRepMin{local= local (syn left)
                                                                                `min` local (syn right)},
                                                   Fork{left= Inherited InhRepMin{global= global $ inh inherited},
                                                        right= Inherited InhRepMin{global= global $ inh inherited}})
   attribution _ _ (inherited, Leaf value) = (Synthesized SynRepMin{local= syn value},
                                              Leaf{leafValue= Inherited InhRepMin{global= global $ inh inherited}})

-- * Helper functions
fork l r = Fork (Identity l) (Identity r)
leaf = Leaf . Identity

data Extractor = Extractor

instance Transformation Extractor where
  type Domain Extractor = AG.Kept RepMin
  type Codomain Extractor = Identity

instance Transformation.At Extractor (Root Int (AG.Kept RepMin) (AG.Kept RepMin)) where
  _ $ AG.Kept{AG.original} = original

instance Transformation.At Extractor (Tree Int (AG.Kept RepMin) (AG.Kept RepMin)) where
--  _ $ AG.Kept{AG.inherited = InhRepMin{global = minimum}, AG.original = Identity Leaf{}} = Identity (Leaf minimum)
  _ $ AG.Kept{AG.original} = original

instance Transformation.At Extractor Int where
  _ $ AG.Kept{AG.inherited = InhRepMin{global = x}} = Identity x

instance Full.Functor Extractor (Tree Int) where
  (<$>) = Full.mapDownDefault

-- | The example tree
exampleTree :: Root Int Identity Identity
exampleTree = Root (Identity $ leaf 7 `fork` (leaf 4 `fork` leaf 1) `fork` leaf 3)

-- |
-- >>> Deep.fmap Extractor $ runIdentity $ AG.original $ Rank2.apply (Full.fmap RepMin $ Identity exampleTree) (Inherited ())
-- Root {root = Identity (Fork {left = Identity (Fork {left = Identity (Leaf {leafValue = Identity 1}), right = Identity (Fork {left = Identity (Leaf {leafValue = Identity 1}), right = Identity (Leaf {leafValue = Identity 1})})}), right = Identity (Leaf {leafValue = Identity 1})})}
