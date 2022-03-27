{-# Language DataKinds, DeriveGeneric, DuplicateRecordFields, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
             StandaloneDeriving, TemplateHaskell, TypeFamilies, UndecidableInstances #-}

-- | The RepMin example with automatic derivation of attributes.

module RepMinAuto where

import Data.Functor.Identity
import Data.Semigroup (Min(Min, getMin))
import GHC.Generics (Generic)
import qualified Rank2
import qualified Rank2.TH
import Transformation (Transformation(..))
import Transformation.AG (Inherited(..), Synthesized(..))
import qualified Transformation
import qualified Transformation.AG as AG
import qualified Transformation.AG.Generics as AG
import Transformation.AG.Generics (Auto(Auto))
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Deep.TH
import qualified Transformation.Shallow.TH

-- | tree data type
data Tree a (f' :: * -> *) (f :: * -> *) = Fork{left :: f (Tree a f' f'),
                                                right:: f (Tree a f' f')}
                                         | Leaf{leafValue :: f a}
-- | tree root
data Root a f' f = Root{root :: f (Tree a f' f')}

deriving instance (Show (f (Tree a f' f')), Show (f a)) => Show (Tree a f' f)
deriving instance (Show (f (Tree a f' f'))) => Show (Root a f' f)

$(concat <$>
  (mapM (\derive-> mconcat <$> mapM derive [''Tree, ''Root])
        [Rank2.TH.deriveFunctor, Rank2.TH.deriveFoldable, Rank2.TH.deriveTraversable, Rank2.TH.unsafeDeriveApply,
         Transformation.Shallow.TH.deriveAll, Transformation.Deep.TH.deriveAll]))

-- | The transformation type. It will always appear wrapped in 'Auto' to enable automatic attribute derivation.
data RepMin = RepMin

-- | The semantics type synonym for convenience
type Sem = AG.Semantics (Auto RepMin)

instance Transformation (Auto RepMin) where
   type Domain (Auto RepMin) = Identity
   type Codomain (Auto RepMin) = Sem

instance AG.Revelation (Auto RepMin) where
   reveal (Auto RepMin) = runIdentity
   
-- | Inherited attributes' type
data InhRepMin = InhRepMin{global :: Int}
               deriving (Generic, Show)

-- | Synthesized attributes' types rely on the 'AG.Folded' and 'AG.Mapped' wrappers, whose rules can be automatically
-- | derived.
data SynRepMin g = SynRepMin{local :: AG.Folded (Min Int),
                             tree  :: AG.Mapped Identity (g Int Identity Identity)}
                   deriving Generic
deriving instance Show (g Int Identity Identity) => Show (SynRepMin g)

-- | Synthesized attributes' type for the integer leaf.
data SynRepLeaf = SynRepLeaf{local :: AG.Folded (Min Int),
                             tree :: AG.Mapped Identity Int}
                  deriving (Generic, Show)

type instance AG.Atts (Inherited RepMin) (Tree Int f' f) = InhRepMin
type instance AG.Atts (Synthesized RepMin) (Tree Int f' f) = SynRepMin Tree
type instance AG.Atts (Inherited RepMin) (Root Int f' f) = ()
type instance AG.Atts (Synthesized RepMin) (Root Int f' f) = SynRepMin Root

type instance AG.Atts (Inherited RepMin) Int = InhRepMin
type instance AG.Atts (Synthesized RepMin) Int = SynRepLeaf

-- | The semantics of the primitive 'Int' type must be defined manually.
instance Transformation.At (Auto RepMin) Int where
   Auto RepMin $ Identity n = Rank2.Arrow f
      where f (Inherited InhRepMin{global= n'}) =
               Synthesized SynRepLeaf{local= AG.Folded (Min n),
                                      tree= AG.Mapped (Identity n')}

-- | The only required attribute rule is the only non-trivial one, where we set the 'global' inherited attribute to
-- | the 'local' minimum synthesized attribute at the tree root.
instance AG.Bequether (Auto RepMin) (Root Int) Sem Identity where
   bequest (Auto RepMin) self inherited (Root (Synthesized SynRepMin{local= rootLocal})) =
      Root{root= Inherited InhRepMin{global= getMin (AG.getFolded rootLocal)}}

-- * Helper functions
fork l r = Fork (Identity l) (Identity r)
leaf = Leaf . Identity

-- | The example tree
exampleTree :: Root Int Identity Identity
exampleTree = Root (Identity $ leaf 7 `fork` (leaf 4 `fork` leaf 1) `fork` leaf 3)

-- |
-- >>> syn $ Rank2.apply (Auto RepMin Transformation.$ Identity (Auto RepMin Deep.<$> exampleTree)) (Inherited ())
-- SynRepMin {local = Folded {getFolded = Min {getMin = 1}}, tree = Mapped {getMapped = Identity (Root {root = Identity (Fork {left = Identity (Fork {left = Identity (Leaf {leafValue = Identity 1}), right = Identity (Fork {left = Identity (Leaf {leafValue = Identity 1}), right = Identity (Leaf {leafValue = Identity 1})})}), right = Identity (Leaf {leafValue = Identity 1})})})}}
