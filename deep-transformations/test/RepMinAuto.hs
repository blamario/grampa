{-# Language DataKinds, DeriveGeneric, DefaultSignatures, DuplicateRecordFields,
             EmptyDataDecls, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, StandaloneDeriving,
             TypeApplications, TypeFamilies, TypeOperators, TypeSynonymInstances, UndecidableInstances #-}

module RepMinAuto where

import Data.Functor.Const
import Data.Functor.Identity
import Data.Semigroup (Min(Min, getMin))
import GHC.Generics (Generic)
import qualified Rank2
import Transformation (Transformation(..))
import Transformation.AG (Inherited(..), Synthesized(..))
import qualified Transformation
import qualified Transformation.AG as AG
import qualified Transformation.AG.Generics as AG
import Transformation.AG.Generics (Auto(Auto))
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Shallow as Shallow

import Debug.Trace

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

instance Rank2.Foldable (Tree a f') where
   f `foldMap` Fork l r = f l <> f r
   f `foldMap` Leaf x = f x

instance Rank2.Foldable (Root a f') where
   f `foldMap` Root x = f x

instance Rank2.Apply (Tree a f') where
   Fork fl fr <*> ~(Fork l r) = Fork (Rank2.apply fl l) (Rank2.apply fr r)
   Leaf f <*> ~(Leaf x) = Leaf (Rank2.apply f x)

instance Rank2.Applicative (Tree a f') where
   pure = Leaf

instance Rank2.Apply (Root a f') where
   Root f <*> ~(Root x) = Root (Rank2.apply f x)

instance (Transformation t, Transformation.At t a, Transformation.At t (Tree a f' f')) => Shallow.Functor t (Tree a f') where
   t <$> Fork l r = Fork (t Transformation.$ l) (t Transformation.$ r)
   t <$> Leaf x = Leaf (t Transformation.$ x)

instance (Transformation t, Transformation.At t (Tree a f' f')) => Shallow.Functor t (Root a f') where
   t <$> Root x = Root (t Transformation.$ x)

instance (Transformation t, Transformation.At t a, Transformation.At t (Tree a f' f')) => Shallow.Foldable t (Tree a f') where
   t `foldMap` Fork l r = getConst (t Transformation.$ l) <> getConst (t Transformation.$ r)
   t `foldMap` Leaf x = getConst (t Transformation.$ x)

instance (Transformation t, Transformation.At t (Tree a f' f')) => Shallow.Foldable t (Root a f') where
   t `foldMap` Root x = getConst (t Transformation.$ x)

instance (Transformation t, Transformation.At t a, Full.Functor t (Tree a)) => Deep.Functor t (Tree a) where
   t <$> Fork l r = Fork (t Full.<$> l) (t Full.<$> r)
   t <$> Leaf x = Leaf (t Transformation.$ x)

instance (Transformation t, Full.Functor t (Tree a)) => Deep.Functor t (Root a) where
   t <$> Root x = Root (t Full.<$> x)

instance (Transformation t, Transformation.At t a,
          Transformation.At t (Tree a (Codomain t) (Codomain t)), Functor(Domain t)) =>
         Full.Functor t (Tree a) where
   (<$>) = Full.mapUpDefault

-- | The transformation type
data RepMin = RepMin

type Sem = AG.Semantics (Auto RepMin)

instance Transformation (Auto RepMin) where
   type Domain (Auto RepMin) = Identity
   type Codomain (Auto RepMin) = Sem

-- | Inherited attributes' type
data InhRepMin = InhRepMin{global :: Int}
               deriving (Generic, Show)

-- | Synthesized attributes' type
data SynRepMin = SynRepMin{local :: AG.Folded (Min Int),
                           tree  :: Tree Int Identity Identity}
               deriving (Generic, Show)

data SynRepLeaf = SynRepLeaf{local :: AG.Folded (Min Int)} deriving (Generic, Show)

type instance AG.Atts (Inherited (Auto RepMin)) (Tree Int f' f) = InhRepMin
type instance AG.Atts (Synthesized (Auto RepMin)) (Tree Int f' f) = SynRepMin
type instance AG.Atts (Inherited (Auto RepMin)) (Root Int f' f) = ()
type instance AG.Atts (Synthesized (Auto RepMin)) (Root Int f' f) = SynRepMin

type instance AG.Atts (Inherited a) Int = InhRepMin
type instance AG.Atts (Synthesized a) Int = SynRepLeaf

instance Transformation.At (Auto RepMin) (Tree Int Sem Sem) where
   ($) = AG.applyDefault runIdentity
instance Transformation.At (Auto RepMin) (Root Int Sem Sem) where
   ($) = AG.applyDefault runIdentity
instance Transformation.At (Auto RepMin) Int where
   Auto RepMin $ Identity n = Rank2.Arrow (const $ Synthesized $ SynRepLeaf $ AG.Folded $ Min n)

instance AG.Bequether (Auto RepMin) (Root Int) Sem Identity where
   bequest (Auto RepMin) self inherited (Root (Synthesized SynRepMin{local= rootLocal})) =
      Root{root= Inherited InhRepMin{global= getMin (AG.getFolded rootLocal)}}

instance AG.SynthesizedField "tree" (Tree Int Identity Identity) (Auto RepMin) (Root Int) Sem Identity where
   synthesizedField _ (Auto RepMin) self inherited (Root root) = tree (syn root)

instance AG.SynthesizedField "tree" (Tree Int Identity Identity) (Auto RepMin) (Tree Int) Sem Identity where
   synthesizedField _ _ _ inherited (Fork left right) = tree (syn left) `fork` tree (syn right)
   synthesizedField _ _ _ inherited (Leaf value) = Leaf{leafValue= Identity $ global inherited}

-- * Helper functions
fork l r = Fork (Identity l) (Identity r)
leaf = Leaf . Identity

-- | The example tree
exampleTree :: Root Int Identity Identity
exampleTree = Root (Identity $ leaf 7 `fork` (leaf 4 `fork` leaf 1) `fork` leaf 3)

-- |
-- >>> tree $ syn $ Rank2.apply (Auto RepMin Transformation.$ Identity (Auto RepMin Deep.<$> exampleTree)) (Inherited ())
-- Fork {left = Identity (Fork {left = Identity (Leaf {leafValue = Identity 1}), right = Identity (Fork {left = Identity (Leaf {leafValue = Identity 1}), right = Identity (Leaf {leafValue = Identity 1})})}), right = Identity (Leaf {leafValue = Identity 1})}
