{-# Language DataKinds, DefaultSignatures, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             InstanceSigs, MultiParamTypeClasses, PolyKinds, RankNTypes, ScopedTypeVariables, StandaloneDeriving,
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
                                   Auto(..), Keep(..), Folded(..), Mapped(..), Traversed(..),
                                   -- * Type classes replacing 'Attribution'
                                   Bequether(..), Synthesizer(..), SynthesizedField(..), Revelation(..),
                                   -- * The default behaviour on generic datatypes
                                   foldedField, mappedField, passDown, bequestDefault)
where

import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
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

-- | Transformation wrapper that allows automatic inference of attribute rules and preservation of all attributes with
-- the original nodes.
newtype Keep t = Keep t

type instance Atts (Inherited (Auto t)) x = Atts (Inherited t) x
type instance Atts (Synthesized (Auto t)) x = Atts (Synthesized t) x

type instance Atts (Inherited (Keep t)) x = Atts (Inherited t) x
type instance Atts (Synthesized (Keep t)) x = Atts (Synthesized t) x

instance {-# overlappable #-} (Transformation (Auto t), Domain (Auto t) ~ f, Codomain (Auto t) ~ Semantics (Auto t),
                               Rank2.Apply (g (Semantics (Auto t))), Attribution (Auto t) g (Semantics (Auto t)) f,
                               Foldable f) =>
                              Auto t `At` g (Semantics (Auto t)) (Semantics (Auto t)) where
   ($) = applyDefault (foldr const $ error "Missing node")
   {-# INLINE ($) #-}

instance {-# overlappable #-}
         (Transformation (Keep t), p ~ Transformation.Domain (Keep t), Foldable p, Rank2.Apply (g q),
          q ~ Transformation.Codomain (Keep t), q ~ PreservingSemantics (Keep t) p, s ~ Semantics (Keep t),
          Atts (Inherited (Keep t)) (g q q) ~ Atts (Inherited (Keep t)) (g s s),
          Atts (Synthesized (Keep t)) (g q q) ~ Atts (Synthesized (Keep t)) (g s s),
          g q (Synthesized (Keep t)) ~ g s (Synthesized (Keep t)),
          g q (Inherited (Keep t)) ~ g s (Inherited (Keep t)), Attribution (Keep t) g q p) =>
         Keep t `At` g (PreservingSemantics (Keep t) p) (PreservingSemantics (Keep t) p) where
   ($) :: Keep t -> p (g (PreservingSemantics (Keep t) p) (PreservingSemantics (Keep t) p))
       -> PreservingSemantics (Keep t) p (g (PreservingSemantics (Keep t) p) (PreservingSemantics (Keep t) p))
   ($) = applyDefaultWithAttributes (foldr const $ error "Missing node")
   {-# INLINE ($) #-}

instance (Transformation (Auto t), Domain (Auto t) ~ f, Functor f, Codomain (Auto t) ~ Semantics (Auto t),
          Deep.Functor (Auto t) g, Auto t `At` g (Semantics (Auto t)) (Semantics (Auto t))) =>
         Full.Functor (Auto t) g where
   (<$>) = Full.mapUpDefault

instance (Transformation (Keep t), Domain (Keep t) ~ f, Functor f, Codomain (Keep t) ~ PreservingSemantics (Keep t) f,
          Functor f, Deep.Functor (Keep t) g,
          Keep t `At` g (PreservingSemantics (Keep t) f) (PreservingSemantics (Keep t) f)) =>
         Full.Functor (Keep t) g where
   (<$>) = Full.mapUpDefault

instance {-# overlappable #-} (Bequether (Auto t) g d s, Synthesizer (Auto t) g d s) => Attribution (Auto t) g d s where
   attribution t l (Inherited i, s) = (Synthesized $ synthesis t l i s, bequest t l i s)

class (Transformation t, dom ~ Domain t) => Revelation t dom where
   -- | Extract the value from the transformation domain
   reveal :: t -> dom x -> x

-- | A half of the 'Attribution' class used to specify all inherited attributes.
class Bequether t g deep shallow where
   bequest     :: forall sem. sem ~ Semantics t =>
                  t                                -- ^ transformation        
               -> shallow (g deep deep)            -- ^ tree node
               -> Atts (Inherited t) (g sem sem)   -- ^ inherited attributes  
               -> g sem (Synthesized t)            -- ^ synthesized attributes
               -> g sem (Inherited t)

-- | A half of the 'Attribution' class used to specify all synthesized attributes.
class Synthesizer t g deep shallow where
   synthesis   :: forall sem. sem ~ Semantics t =>
                  t                                -- ^ transformation        
               -> shallow (g deep deep)            -- ^ tree node
               -> Atts (Inherited t) (g sem sem)   -- ^ inherited attributes  
               -> g sem (Synthesized t)            -- ^ synthesized attributes
               -> Atts (Synthesized t) (g sem sem)

-- | Class for specifying a single named attribute
class SynthesizedField (name :: Symbol) result t g deep shallow where
   synthesizedField  :: forall sem. sem ~ Semantics t =>
                        Proxy name                      -- ^ attribute name
                     -> t                               -- ^ transformation
                     -> shallow (g deep deep)           -- ^ tree node
                     -> Atts (Inherited t) (g sem sem)  -- ^ inherited attributes
                     -> g sem (Synthesized t)           -- ^ synthesized attributes
                     -> result

instance (Transformation t, Domain t ~ Identity) => Revelation t Identity where
   reveal _ (Identity x) = x

instance (Transformation t, Domain t ~ (,) a) => Revelation t ((,) a) where
   reveal _ (_, x) = x

instance {-# overlappable #-} (sem ~ Semantics t, Domain t ~ shallow, Revelation t shallow,
                               Shallow.Functor (PassDown t sem (Atts (Inherited t) (g sem sem))) (g sem)) =>
                              Bequether t g (Semantics t) shallow where
   bequest = bequestDefault

instance {-# overlappable #-} (Atts (Synthesized t) (g sem sem) ~ result, Generic result, sem ~ Semantics t,
                               GenericSynthesizer t g d s (Rep result)) => Synthesizer t g d s where
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
newtype Traversed m f a = Traversed{getTraversed :: m (f a)} deriving (Eq, Ord, Show, Semigroup, Monoid)

instance (Functor m, Functor f) => Functor (Traversed m f) where
   fmap f (Traversed x) = Traversed ((f <$>) <$> x)

-- * Generic transformations

-- | Internal transformation for passing down the inherited attributes.
newtype PassDown (t :: Type) (f :: * -> *) a = PassDown a
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

instance Subtype (Atts (Inherited t) a) b => Transformation.At (PassDown t f b) a where
   ($) (PassDown i) _ = Inherited (upcast i)

instance (Monoid a, r ~ Atts (Synthesized t) x, Generic r, MayHaveMonoidalField name (Folded a) (Rep r)) =>
         Transformation.At (Accumulator t name a) x where
   _ $ Synthesized r = Const (getMonoidalField (Proxy :: Proxy name) $ from r)

instance (HasField name (Atts (Synthesized t) a) (Mapped f a)) => Transformation.At (Replicator t f name) a where
   _ $ Synthesized r = getMapped (getField @name r)

instance (HasField name (Atts (Synthesized t) a) (Traversed m f a)) => Transformation.At (Traverser t m f name) a where
   _ $ Synthesized r = Compose (getTraversed $ getField @name r)

-- * Generic classes

-- | The 'Generic' mirror of 'Synthesizer'
class GenericSynthesizer t g deep shallow result where
   genericSynthesis  :: forall a sem. sem ~ Semantics t =>
                        t
                     -> shallow (g deep deep)
                     -> Atts (Inherited t) (g sem sem)
                     -> g sem (Synthesized t)
                     -> result a

-- | The 'Generic' mirror of 'SynthesizedField'
class GenericSynthesizedField (name :: Symbol) result t g deep shallow where
   genericSynthesizedField  :: forall a sem. sem ~ Semantics t =>
                               Proxy name
                            -> t
                            -> shallow (g deep deep)
                            -> Atts (Inherited t) (g sem sem)
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

instance (GenericSynthesizer t g deep shallow x, GenericSynthesizer t g deep shallow y) =>
         GenericSynthesizer t g deep shallow (x :*: y) where
   genericSynthesis t node i s = genericSynthesis t node i s :*: genericSynthesis t node i s

instance {-# overlappable #-} GenericSynthesizer t g deep shallow f =>
                              GenericSynthesizer t g deep shallow (M1 i meta f) where
   genericSynthesis t node i s = M1 (genericSynthesis t node i s)

instance {-# overlaps #-} GenericSynthesizedField name f t g deep shallow =>
                          GenericSynthesizer t g deep shallow (M1 i ('MetaSel ('Just name) su ss ds) f) where
   genericSynthesis t node i s = M1 (genericSynthesizedField (Proxy :: Proxy name) t node i s)

instance SynthesizedField name a t g deep shallow => GenericSynthesizedField name (K1 i a) t g deep shallow where
   genericSynthesizedField name t node i s = K1 (synthesizedField name t node i s)

instance  {-# overlappable #-} (Monoid a, Shallow.Foldable (Accumulator t name a) (g (Semantics t))) =>
                               SynthesizedField name (Folded a) t g deep shallow where
   synthesizedField name t _ _ s = foldedField name t s

instance  {-# overlappable #-} (Functor f, Shallow.Functor (Replicator t f name) (g f),
                                Atts (Synthesized t) (g (Semantics t) (Semantics t)) ~ Atts (Synthesized t) (g f f)) =>
                               SynthesizedField name (Mapped f (g f f)) t g deep f where
   synthesizedField name t local _ s = Mapped (mappedField name t s <$ local)

instance  {-# overlappable #-} (Traversable f, Applicative m, Shallow.Traversable (Traverser t m f name) (g f),
                                Atts (Synthesized t) (g (Semantics t) (Semantics t)) ~ Atts (Synthesized t) (g f f)) =>
                               SynthesizedField name (Traversed m f (g f f)) t g deep f where
   synthesizedField name t local _ s = Traversed (traverse (const $ traversedField name t s) local)

-- | The default 'bequest' method definition relies on generics to automatically pass down all same-named inherited
-- attributes.
bequestDefault :: forall t g shallow sem.
                  (sem ~ Semantics t, Domain t ~ shallow, Revelation t shallow,
                   Shallow.Functor (PassDown t sem (Atts (Inherited t) (g sem sem))) (g sem))
               => t -> shallow (g sem sem) -> Atts (Inherited t) (g sem sem) -> g sem (Synthesized t)
               -> g sem (Inherited t)
bequestDefault t local inheritance _synthesized = passDown inheritance (reveal t local)

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
                  (Shallow.Functor (Replicator t f name) (g f),
                   Atts (Synthesized t) (g sem sem) ~ Atts (Synthesized t) (g f f)) =>
                  Proxy name -> t -> g sem (Synthesized t) -> g f f
mappedField _name _t s = (Replicator :: Replicator t f name) Shallow.<$> (unsafeCoerce s :: g f (Synthesized t))

-- | The default 'synthesizedField' method definition for 'Traversed' fields.
traversedField :: forall name t g m f sem.
                     (Shallow.Traversable (Traverser t m f name) (g f),
                      Atts (Synthesized t) (g sem sem) ~ Atts (Synthesized t) (g f f)) =>
                     Proxy name -> t -> g sem (Synthesized t) -> m (g f f)
traversedField _name _t s = Shallow.traverse (Traverser :: Traverser t m f name) (unsafeCoerce s :: g f (Synthesized t))
