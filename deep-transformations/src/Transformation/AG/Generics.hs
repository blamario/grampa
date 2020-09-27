{-# Language DataKinds, DefaultSignatures, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, PolyKinds, RankNTypes, ScopedTypeVariables, StandaloneDeriving,
             TypeApplications, TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation.AG.Generics (Auto(..), Folded(..), Mapped(..),
                                   Bequether(..), Synthesizer(..), SynthesizedField(..), Revelation(..),
                                   foldedField, mappedField)
where

import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Kind (Type)
import Data.Generics.Product.Subtype (Subtype(upcast))
import Data.Proxy (Proxy(..))
import GHC.Generics
import qualified GHC.Generics as Generics
import GHC.Records
import GHC.TypeLits (Symbol, KnownSymbol, SomeSymbol(..), ErrorMessage (Text), TypeError)
import Unsafe.Coerce (unsafeCoerce)
import qualified Rank2
import Transformation (Transformation, Domain, Codomain)
import Transformation.AG
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Shallow as Shallow

newtype Auto t = Auto t

instance {-# overlappable #-} (Bequether (Auto t) g d s, sem ~ Semantics (Auto t), Synthesizer (Auto t) g d s) =>
                              Attribution (Auto t) g d s where
   attribution t l (Inherited i, s) = (Synthesized $ synthesis t l i s, bequest t l i s)

class Transformation t => Revelation t where
   reveal :: t -> Domain t x -> x

class Bequether t g deep shallow where
   bequest     :: forall sem. sem ~ Semantics t =>
                  t
               -> shallow (g deep deep)
               -> Atts (Inherited t) (g sem sem)
               -> g sem (Synthesized t)
               -> g sem (Inherited t)

class Synthesizer t g deep shallow where
   synthesis   :: forall sem. sem ~ Semantics t =>
                  t
               -> shallow (g deep deep)
               -> Atts (Inherited t) (g sem sem)
               -> g sem (Synthesized t)
               -> Atts (Synthesized t) (g sem sem)

class SynthesizedField (name :: Symbol) result t g deep shallow where
   synthesizedField  :: forall sem. sem ~ Semantics t =>
                        Proxy name
                     -> t
                     -> shallow (g deep deep)
                     -> Atts (Inherited t) (g sem sem)
                     -> g sem (Synthesized t)
                     -> result

instance {-# overlappable #-} (sem ~ Semantics t, Domain t ~ shallow, Revelation t,
                               Shallow.Functor (PassDown t sem (Atts (Inherited t) (g sem sem))) (g sem)) =>
                              Bequether t g (Semantics t) shallow where
   bequest = bequestDefault

instance {-# overlappable #-} (Atts (Synthesized t) (g sem sem) ~ result, Generic result, sem ~ Semantics t,
                               GenericSynthesizer t g d s (Rep result)) => Synthesizer t g d s where
   synthesis t node i s = to (genericSynthesis t node i s)

newtype Folded a = Folded{getFolded :: a} deriving (Eq, Ord, Show, Semigroup, Monoid)
newtype Mapped f a = Mapped{getMapped :: f a}
                   deriving (Eq, Ord, Show, Semigroup, Monoid, Functor, Applicative, Monad, Foldable)

-- * Generic transformations

newtype PassDown (t :: Type) (f :: * -> *) a = PassDown a
data Accumulator (t :: Type) (name :: Symbol) (a :: Type) = Accumulator
data Replicator (t :: Type) (f :: Type -> Type) (name :: Symbol) = Replicator

instance Transformation (PassDown t f a) where
  type Domain (PassDown t f a) = f
  type Codomain (PassDown t f a) = Inherited t

instance Transformation (Accumulator t name a) where
  type Domain (Accumulator t name a) = Synthesized t
  type Codomain (Accumulator t name a) = Const (Folded a)

instance Transformation (Replicator t f name) where
  type Domain (Replicator t f name) = Synthesized t
  type Codomain (Replicator t f name) = f

instance Subtype (Atts (Inherited t) a) b => Transformation.At (PassDown t f b) a where
   ($) (PassDown i) _ = Inherited (upcast i)

instance (Monoid a, r ~ Atts (Synthesized t) x, Generic r, MayHaveMonoidalField name (Folded a) (Rep r)) =>
         Transformation.At (Accumulator t name a) x where
   _ $ Synthesized r = Const (getMonoidalField (Proxy :: Proxy name) $ from r)

instance (HasField name (Atts (Synthesized t) a) (Mapped f a)) => Transformation.At (Replicator t f name) a where
   _ $ Synthesized r = getMapped (getField @name r)

-- * Generic classes

class GenericSynthesizer t g deep shallow result where
   genericSynthesis  :: forall a sem. sem ~ Semantics t =>
                        t
                     -> shallow (g deep deep)
                     -> Atts (Inherited t) (g sem sem)
                     -> g sem (Synthesized t)
                     -> result a

class GenericSynthesizedField (name :: Symbol) result t g deep shallow where
   genericSynthesizedField  :: forall a sem. sem ~ Semantics t =>
                               Proxy name
                            -> t
                            -> shallow (g deep deep)
                            -> Atts (Inherited t) (g sem sem)
                            -> g sem (Synthesized t)
                            -> result a

class MayHaveMonoidalField (name :: Symbol) a f where
   getMonoidalField :: Proxy name -> f x -> a

instance {-# overlaps #-} (MayHaveMonoidalField name a x, MayHaveMonoidalField name a y, Semigroup a) =>
         MayHaveMonoidalField name a (x :*: y) where
   getMonoidalField name (x :*: y) = getMonoidalField name x <> getMonoidalField name y

instance {-# overlaps #-} TypeError (Text "Cannot get a single field value from a sum type") =>
         MayHaveMonoidalField name a (x :+: y) where
   getMonoidalField _ _ = error "getMonoidalField on sum type"

instance {-# overlaps #-} MayHaveMonoidalField name a (M1 i ('MetaSel ('Just name) su ss ds) (K1 j a)) where
   getMonoidalField name (M1 (K1 v)) = v

instance {-# overlappable #-} Monoid a => MayHaveMonoidalField name a f where
   getMonoidalField name _ = mempty

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

bequestDefault, passDown :: forall sem shallow t g.
                            (sem ~ Semantics t, Domain t ~ shallow, Revelation t,
                             Shallow.Functor (PassDown t sem (Atts (Inherited t) (g sem sem))) (g sem))
                         => t -> shallow (g sem sem)
                         -> Atts (Inherited t) (g sem sem)
                         -> g sem (Synthesized t)
                         -> g sem (Inherited t)
bequestDefault t local inheritance synthesized = PassDown inheritance Shallow.<$> reveal t local
passDown = bequestDefault

foldedField :: forall name t g deep shallow a. (Monoid a, Shallow.Foldable (Accumulator t name a) (g (Semantics t))) =>
              Proxy name -> t -> g (Semantics t) (Synthesized t) -> Folded a
foldedField name t s = Shallow.foldMap (Accumulator :: Accumulator t name a) s

mappedField :: forall name t g deep shallow f a.
                  (Shallow.Functor (Replicator t f name) (g f),
                   Atts (Synthesized t) (g (Semantics t) (Semantics t)) ~ Atts (Synthesized t) (g f f)) =>
                  Proxy name -> t -> g (Semantics t) (Synthesized t) -> g f f
mappedField name t s = (Replicator :: Replicator t f name) Shallow.<$> (unsafeCoerce s :: g f (Synthesized t))
