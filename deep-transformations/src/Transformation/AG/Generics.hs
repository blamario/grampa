{-# Language DataKinds, DefaultSignatures, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             InstanceSigs, MultiParamTypeClasses, PolyKinds, QuantifiedConstraints,
             RankNTypes, ScopedTypeVariables, StandaloneDeriving,
             TypeApplications, TypeFamilies, TypeOperators, UndecidableInstances #-}

-- | This module can be used to scrap the boilerplate attribute declarations. In particular:
--
-- * If an 'attribution' rule always merely copies the inherited attributes to the children's inherited attributes of
--   the same name, the rule can be left out by wrapping the transformation into an 'Auto' constructor and deriving
--   the 'Generic' instance of the inherited attributes.
-- * A synthesized attribute whose value is a fold of all same-named attributes of the children can be wrapped in the
--   'Folded' constructor and calculated automatically.
-- * A synthesized attribute that is a copy of the current node but with every child taken from the same-named
--   synthesized child attribute can be wrapped in the 'Mapped' constructor and calculated automatically.
-- * If the attribute additionally carries an applicative effect, the 'Mapped' wrapper can be replaced by 'Traversed'.

module Transformation.AG.Generics (-- * Type wrappers for automatic attribute inference
                                   Auto(..), Folded(..), Mapped(..), Traversed(..),
                                   -- * Type classes replacing 'Attribution'
                                   Bequether(..), Synthesizer(..), SynthesizedField(..), Revelation(..),
                                   -- * The default behaviour on generic datatypes
                                   foldedField, mappedField, passDown, bequestDefault)
where

import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Kind (Type)
import Data.Generics.Product.Subtype (Subtype(upcast))
import Data.Proxy (Proxy(..))
import GHC.Generics
import GHC.Records
import GHC.TypeLits (Symbol, ErrorMessage (Text), TypeError)
import Unsafe.Coerce (unsafeCoerce)
import qualified Rank2
import Transformation (Transformation, Domain, Codomain, At)
import Transformation.AG
import qualified Transformation
import qualified Transformation.Shallow as Shallow
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

-- | Transformation wrapper that allows automatic inference of attribute rules.
newtype Auto t = Auto t

type instance Atts (Inherited (Auto t)) x = Atts (Inherited t) x
type instance Atts (Synthesized (Auto t)) x = Atts (Synthesized t) x

instance {-# overlappable #-} (Revelation (Auto t), Domain (Auto t) ~ f, Codomain (Auto t) ~ Semantics (Auto t),
                               Rank2.Apply (g (Semantics (Auto t))), Attribution (Auto t) g f) =>
                              Auto t `At` g (Semantics (Auto t)) (Semantics (Auto t)) where
   t $ x = applyDefault (reveal t) t x
   {-# INLINE ($) #-}


instance (Transformation (Auto t), Domain (Auto t) ~ f, Functor f, Codomain (Auto t) ~ Semantics (Auto t),
          Rank2.Functor (g f), Deep.Functor (Auto t) g, Auto t `At` g (Semantics (Auto t)) (Semantics (Auto t))) =>
         Full.Functor (Auto t) g where
   (<$>) = Full.mapUpDefault
instance {-# overlappable #-} (Bequether (Auto t) g s, Synthesizer (Auto t) g s) => Attribution (Auto t) g s where
   attribution t l (Inherited i, s) = (Synthesized $ synthesis t l i s, bequest t l i s)

class Transformation t => Revelation t where
   -- | Extract the value from the transformation domain
   reveal :: t -> Domain t x -> x

-- | A half of the 'Attribution' class used to specify all inherited attributes.
class Bequether t g shallow where
   bequest     :: forall sem deep. sem ~ Semantics t =>
                  t                                -- ^ transformation        
               -> shallow (g deep deep)            -- ^ tree node
               -> Atts (Inherited t) g             -- ^ inherited attributes
               -> g sem (Synthesized t)            -- ^ synthesized attributes
               -> g sem (Inherited t)

-- | A half of the 'Attribution' class used to specify all synthesized attributes.
class Synthesizer t g shallow where
   synthesis   :: forall sem deep. sem ~ Semantics t =>
                  t                                -- ^ transformation        
               -> shallow (g deep deep)            -- ^ tree node
               -> Atts (Inherited t) g             -- ^ inherited attributes
               -> g sem (Synthesized t)            -- ^ synthesized attributes
               -> Atts (Synthesized t) g

-- | Class for specifying a single named attribute
class SynthesizedField (name :: Symbol) result t g shallow where
   synthesizedField  :: forall sem deep. sem ~ Semantics t =>
                        Proxy name                      -- ^ attribute name
                     -> t                               -- ^ transformation
                     -> shallow (g deep deep)           -- ^ tree node
                     -> Atts (Inherited t) g            -- ^ inherited attributes
                     -> g sem (Synthesized t)           -- ^ synthesized attributes
                     -> result

instance {-# overlappable #-} (Domain t ~ shallow, Revelation t, a ~ Atts (Inherited t) g,
                               forall deep. Shallow.Functor (PassDown t deep a) (g deep)) =>
                              Bequether t g shallow where
   bequest     :: forall sem deep. sem ~ Semantics t =>
                  t                                -- ^ transformation        
               -> shallow (g deep deep)            -- ^ tree node
               -> Atts (Inherited t) g             -- ^ inherited attributes
               -> g sem (Synthesized t)            -- ^ synthesized attributes
               -> g sem (Inherited t)
   bequest = bequestDefault

instance {-# overlappable #-} (Atts (Synthesized t) g ~ result, Generic result, sem ~ Semantics t,
                               GenericSynthesizer t g s (Rep result)) => Synthesizer t g s where
   synthesis t node i s = to (genericSynthesis t node i s)

-- | Wrapper for a field that should be automatically synthesized by folding together all child nodes' synthesized
-- attributes of the same name.
newtype Folded a = Folded{getFolded :: a} deriving (Eq, Ord, Show, Semigroup, Monoid)
-- | Wrapper for a field that should be automatically synthesized by replacing every child node by its synthesized
-- attribute of the same name.
newtype Mapped f a = Mapped{getMapped :: f a}
                   deriving (Eq, Ord, Show, Semigroup, Monoid, Functor, Applicative, Monad, Foldable)

-- | Wrapper for a field that should be automatically synthesized by traversing over all child nodes and applying each
-- node's synthesized attribute of the same name.
newtype Traversed m f g = Traversed{getTraversed :: m (f (g f f))} --deriving (Eq, Ord, Show, Semigroup, Monoid)

-- * Generic transformations

-- | Internal transformation for passing down the inherited attributes.
newtype PassDown (t :: Type) (f :: Type -> Type) a = PassDown a
-- | Internal transformation for accumulating the 'Folded' attributes.
data Accumulator (t :: Type) (name :: Symbol) (a :: Type) = Accumulator
-- | Internal transformation for replicating the 'Mapped' attributes.
data Replicator (t :: Type) (f :: Type -> Type) (name :: Symbol) = Replicator
-- | Internal transformation for traversing the 'Traversed' attributes.
data Traverser (t :: Type) (m :: Type -> Type) (f :: Type -> Type) (name :: Symbol) = Traverser

instance Transformation (PassDown t f a) where
  type Domain (PassDown t f a) = f
  type Codomain (PassDown t f a) = Inherited t

instance Transformation (Accumulator t name a) where
  type Domain (Accumulator t name a) = Synthesized t
  type Codomain (Accumulator t name a) = Const (Folded a)

instance Transformation (Replicator t f name) where
  type Domain (Replicator t f name) = Synthesized t
  type Codomain (Replicator t f name) = f

instance Transformation (Traverser t m f name) where
  type Domain (Traverser t m f name) = Synthesized t
  type Codomain (Traverser t m f name) = Compose m f

instance Subtype (Atts (Inherited t) (NodeConstructor a)) b => Transformation.At (PassDown t f b) a where
   ($) (PassDown i) _ = Inherited (upcast i)

instance (Monoid a, r ~ Atts (Synthesized t) (NodeConstructor x), Generic r,
          MayHaveMonoidalField name (Folded a) (Rep r)) =>
         Transformation.At (Accumulator t name a) x where
   _ $ Synthesized r = Const (getMonoidalField (Proxy :: Proxy name) $ from r)

instance (HasField name (Atts (Synthesized t) (NodeConstructor a)) (Mapped f a)) => Transformation.At (Replicator t f name) a where
   _ $ Synthesized r = getMapped (getField @name r)

instance (HasField name (Atts (Synthesized t) g) (Traversed m f g)) =>
         Transformation.At (Traverser t m f name) (g f f) where
   _ $ Synthesized r = Compose (getTraversed $ getField @name r)

-- * Generic classes

-- | The 'Generic' mirror of 'Synthesizer'
class GenericSynthesizer t g shallow result where
   genericSynthesis  :: forall a sem deep. sem ~ Semantics t =>
                        t
                     -> shallow (g deep deep)
                     -> Atts (Inherited t) g
                     -> g sem (Synthesized t)
                     -> result a

-- | The 'Generic' mirror of 'SynthesizedField'
class GenericSynthesizedField (name :: Symbol) result t g shallow where
   genericSynthesizedField  :: forall a sem deep. sem ~ Semantics t =>
                               Proxy name
                            -> t
                            -> shallow (g deep deep)
                            -> Atts (Inherited t) g
                            -> g sem (Synthesized t)
                            -> result a

-- | Used for accumulating the 'Folded' fields 
class MayHaveMonoidalField (name :: Symbol) a f where
   getMonoidalField :: Proxy name -> f x -> a
class FoundField a f where
   getFoundField :: f x -> a

instance {-# overlaps #-} (MayHaveMonoidalField name a x, MayHaveMonoidalField name a y, Semigroup a) =>
         MayHaveMonoidalField name a (x :*: y) where
   getMonoidalField name (x :*: y) = getMonoidalField name x <> getMonoidalField name y

instance {-# overlaps #-} TypeError ('Text "Cannot get a single field value from a sum type") =>
         MayHaveMonoidalField name a (x :+: y) where
   getMonoidalField _ _ = error "getMonoidalField on sum type"

instance {-# overlaps #-} FoundField a f => MayHaveMonoidalField name a (M1 i ('MetaSel ('Just name) su ss ds) f) where
   getMonoidalField _ (M1 x) = getFoundField x

instance {-# overlaps #-} Monoid a => MayHaveMonoidalField name a (M1 i ('MetaSel 'Nothing su ss ds) f) where
   getMonoidalField _ _ = mempty

instance {-# overlaps #-} MayHaveMonoidalField name a f => MayHaveMonoidalField name a (M1 i ('MetaData n m p nt) f) where
   getMonoidalField name (M1 x) = getMonoidalField name x

instance {-# overlaps #-} MayHaveMonoidalField name a f => MayHaveMonoidalField name a (M1 i ('MetaCons n fi s) f) where
   getMonoidalField name (M1 x) = getMonoidalField name x

instance {-# overlappable #-} Monoid a => MayHaveMonoidalField name a f where
   getMonoidalField _ _ = mempty

instance FoundField a f => FoundField a (M1 i j f) where
     getFoundField (M1 f) = getFoundField f

instance FoundField a (K1 i a) where
     getFoundField (K1 a) = a

instance (GenericSynthesizer t g shallow x, GenericSynthesizer t g shallow y) =>
         GenericSynthesizer t g shallow (x :*: y) where
   genericSynthesis t node i s = genericSynthesis t node i s :*: genericSynthesis t node i s

instance {-# overlappable #-} GenericSynthesizer t g shallow f =>
                              GenericSynthesizer t g shallow (M1 i meta f) where
   genericSynthesis t node i s = M1 (genericSynthesis t node i s)

instance {-# overlaps #-} GenericSynthesizedField name f t g shallow =>
                          GenericSynthesizer t g shallow (M1 i ('MetaSel ('Just name) su ss ds) f) where
   genericSynthesis t node i s = M1 (genericSynthesizedField (Proxy :: Proxy name) t node i s)

instance SynthesizedField name a t g shallow => GenericSynthesizedField name (K1 i a) t g shallow where
   genericSynthesizedField name t node i s = K1 (synthesizedField name t node i s)

instance  {-# overlappable #-} (Monoid a, Shallow.Foldable (Accumulator t name a) (g (Semantics t))) =>
                               SynthesizedField name (Folded a) t g shallow where
   synthesizedField name t _ _ s = foldedField name t s

instance  {-# overlappable #-} (Functor f, Shallow.Functor (Replicator t f name) (g f)) =>
                               SynthesizedField name (Mapped f (g f f)) t g f where
   synthesizedField name t local _ s = Mapped (mappedField name t s <$ local)

instance  {-# overlappable #-} (Traversable f, Applicative m, Shallow.Traversable (Traverser t m f name) (g f)) =>
                               SynthesizedField name (Traversed m f g) t g f where
   synthesizedField name t local _ s = Traversed (traverse (const $ traversedField name t s) local)

-- | The default 'bequest' method definition relies on generics to automatically pass down all same-named inherited
-- attributes.
bequestDefault :: forall t g deep shallow sem.
                  (sem ~ Semantics t, Domain t ~ shallow, Revelation t,
                   Shallow.Functor (PassDown t deep (Atts (Inherited t) g)) (g deep))
               => t -> shallow (g deep deep) -> Atts (Inherited t) g -> g sem (Synthesized t)
               -> g sem (Inherited t)
bequestDefault t local inheritance _synthesized = unsafeCoerce $ passDown @t inheritance (reveal t local :: g deep deep)

-- | Pass down the given record of inherited fields to child nodes.
passDown :: forall t g shallow deep atts. (Shallow.Functor (PassDown t shallow atts) (g deep)) =>
            atts -> g deep shallow -> g deep (Inherited t)
passDown inheritance local = PassDown inheritance Shallow.<$> local

-- | The default 'synthesizedField' method definition for 'Folded' fields.
foldedField :: forall name t g a sem. (Monoid a, Shallow.Foldable (Accumulator t name a) (g sem)) =>
               Proxy name -> t -> g sem (Synthesized t) -> Folded a
foldedField _name _t s = Shallow.foldMap (Accumulator :: Accumulator t name a) s

-- | The default 'synthesizedField' method definition for 'Mapped' fields.
mappedField :: forall name t g f sem.
                  (Shallow.Functor (Replicator t f name) (g f)) =>
                  Proxy name -> t -> g sem (Synthesized t) -> g f f
mappedField _name _t s = (Replicator :: Replicator t f name) Shallow.<$> (unsafeCoerce s :: g f (Synthesized t))

-- | The default 'synthesizedField' method definition for 'Traversed' fields.
traversedField :: forall name t g m f sem.
                     (Shallow.Traversable (Traverser t m f name) (g f)) =>
                     Proxy name -> t -> g sem (Synthesized t) -> m (g f f)
traversedField _name _t s = Shallow.traverse (Traverser :: Traverser t m f name) (unsafeCoerce s :: g f (Synthesized t))
