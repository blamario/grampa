{-# Language DefaultSignatures, EmptyDataDecls, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             ConstraintKinds, MultiParamTypeClasses, RankNTypes, StandaloneDeriving, 
             TypeApplications, TypeFamilies, TypeOperators, TypeSynonymInstances, UndecidableInstances #-}

module RepMin where

import Data.Functor.Identity
import qualified Rank2
import Transformation (Transformation(..))
import Transformation.AG (Inherited(..), Synthesized(..))
import qualified Transformation
import qualified Transformation.AG as AG
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

-- | tree data type
data Tree a (f' :: * -> *) (f :: * -> *) = Fork{left :: f (Tree a f' f'),
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

instance Rank2.Apply (Tree a f') where
   Fork fl fr <*> ~(Fork l r) = Fork (Rank2.apply fl l) (Rank2.apply fr r)
   Leaf f <*> ~(Leaf x) = Leaf (Rank2.apply f x)

instance Rank2.Applicative (Tree a f') where
   pure = Leaf

instance Rank2.Apply (Root a f') where
   Root f <*> ~(Root x) = Root (Rank2.apply f x)

instance (Transformation t, Transformation.At t a, Full.Functor t (Tree a)) => Deep.Functor t (Tree a) where
   t <$> Fork l r = Fork (t Full.<$> l) (t Full.<$> r)
   t <$> Leaf x = Leaf (t Transformation.$ x)

instance (Transformation t, Full.Functor t (Tree a)) => Deep.Functor t (Root a) where
   t <$> Root x = Root (t Full.<$> x)

-- | The transformation type
data RepMin = RepMin

instance Transformation RepMin where
   type Domain RepMin = Identity
   type Codomain RepMin = AG.Semantics RepMin

-- | Inherited attributes' type
data InhRepMin = InhRepMin{global :: Int}
               deriving Show

-- | Synthesized attributes' type
data SynRepMin = SynRepMin{local :: Int,
                           tree  :: Tree Int Identity Identity}
               deriving Show

type instance AG.Atts (Inherited RepMin) (Tree Int f' f) = InhRepMin
type instance AG.Atts (Synthesized RepMin) (Tree Int f' f) = SynRepMin
type instance AG.Atts (Inherited RepMin) (Root Int f' f) = ()
type instance AG.Atts (Synthesized RepMin) (Root Int f' f) = SynRepMin

type instance AG.Atts (Inherited a) Int = ()
type instance AG.Atts (Synthesized a) Int = Int

instance Full.Functor RepMin (Tree Int) where
  (<$>) = AG.fullMapDefault runIdentity
instance Full.Functor RepMin (Root Int) where
  (<$>) = AG.fullMapDefault runIdentity

instance Transformation.At RepMin Int where
   RepMin $ Identity n = Rank2.Arrow (const $ Synthesized n)

instance AG.Attribution RepMin (Root Int) Identity Identity where
   attribution RepMin self (inherited, Root root) = (Synthesized SynRepMin{local= local (syn root),
                                                                           tree= tree (syn root)},
                                                     Root{root= Inherited InhRepMin{global= local (syn root)}})

instance AG.Attribution RepMin (Tree Int) Identity Identity where
   attribution _ _ (inherited, Fork left right) = (Synthesized SynRepMin{local= local (syn left) `min` local (syn right),
                                                                         tree= tree (syn left) `fork` tree (syn right)},
                                                   Fork{left= Inherited InhRepMin{global= global $ inh inherited},
                                                        right= Inherited InhRepMin{global= global $ inh inherited}})
   attribution _ _ (inherited, Leaf value) = (Synthesized SynRepMin{local= syn value,
                                                                    tree= Leaf{leafValue= Identity $ global
                                                                                          $ inh inherited}},
                                              Leaf{leafValue= Inherited ()})

-- * Helper functions
fork l r = Fork (Identity l) (Identity r)
leaf = Leaf . Identity

-- | The example tree
exampleTree :: Root Int Identity Identity
exampleTree = Root (Identity $ leaf 7 `fork` (leaf 4 `fork` leaf 1) `fork` leaf 3)

-- |
-- >>> Rank2.apply (Full.fmap RepMin $ Identity exampleTree) (Inherited ())
-- Synthesized {syn = SynRepMin {local = 1, tree = Fork {left = Identity (Fork {left = Identity (Leaf {leafValue = Identity 1}), right = Identity (Fork {left = Identity (Leaf {leafValue = Identity 1}), right = Identity (Leaf {leafValue = Identity 1})})}), right = Identity (Leaf {leafValue = Identity 1})}}}
