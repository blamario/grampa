{-# Language DataKinds, DefaultSignatures, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, PolyKinds, RankNTypes, ScopedTypeVariables, StandaloneDeriving,
             TypeApplications, TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation.AG.Generics where

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
import qualified Rank2
import Transformation (Transformation, Domain, Codomain)
import Transformation.AG
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Shallow as Shallow

class Synthesizer' t g deep shallow result where
   synthesis'  :: forall a sem. sem ~ Semantics t =>
                  t -> shallow (g deep deep)
               -> Atts (Inherited t) (g sem sem)
               -> g sem (Synthesized t)
               -> result a

class SynthesizerField t g deep shallow (name :: Symbol) result where
   synthesisF  :: forall a sem. sem ~ Semantics t =>
                  t -> shallow (g deep deep)
               -> Atts (Inherited t) (g sem sem)
               -> g sem (Synthesized t)
               -> Proxy name
               -> result

class SynthesizerField' t g deep shallow (name :: Symbol) result where
   synthesisF'  :: forall a sem. sem ~ Semantics t =>
                   t -> shallow (g deep deep)
                -> Atts (Inherited t) (g sem sem)
                -> g sem (Synthesized t)
                -> Proxy name
                -> result a

instance {-# overlappable #-} (sem ~ Semantics t, Domain t ~ shallow, Revelation t,
                               Shallow.Functor (PassDown t sem (Atts (Inherited t) (g sem sem))) (g sem)) =>
                              Bequether t g (Semantics t) shallow where
   bequest = bequestDefault

instance (Atts (Synthesized t) (g sem sem) ~ result, Generic result, sem ~ Semantics t,
          Synthesizer' t g d s (Rep result)) => Synthesizer t g d s where
   synthesis t node i s = to (synthesis' t node i s)

newtype PassDown (t :: Type) (f :: * -> *) a = PassDown a
newtype Accumulated a = Accumulated a
newtype Replicated m n a = Replicated (m a)
data Accumulator (t :: Type) (name :: Symbol) (a :: Type) = Accumulator
data Replicator (t :: Type) (m :: Type -> Type) (n :: Type -> Type) (name :: Symbol) (a :: Type) = Replicator

instance Transformation (PassDown t f a) where
  type Domain (PassDown t f a) = f
  type Codomain (PassDown t f a) = Inherited t

instance Transformation (Accumulator t name a) where
  type Domain (Accumulator t name a) = Synthesized t
  type Codomain (Accumulator t name a) = Const a

instance Transformation (Replicator t m n name a) where
  type Domain (Replicator t m n name a) = Synthesized t
  type Codomain (Replicator t m n name a) = Compose m n

instance Subtype (Atts (Inherited t) a) b => Transformation.At (PassDown t f b) a where
   ($) (PassDown i) _ = Inherited (upcast i)

instance (Monoid a, r ~ Atts (Synthesized t) x, Generic r, MayHaveMonoidalField name a (Rep r)) =>
         Transformation.At (Accumulator t name a) x where
   _ $ Synthesized r = Const (getMonoidalField (Proxy :: Proxy name) $ from r)

instance (Applicative m, Applicative n, HasField name (Atts (Synthesized t) a) a) =>
         Transformation.At (Replicator t m n name a) a where
   _ $ Synthesized r = pure (getField @name r)

class MayHaveMonoidalField (name :: Symbol) a f where
   getMonoidalField :: Proxy name -> f x -> a

instance (MayHaveMonoidalField name a x, MayHaveMonoidalField name a y, Semigroup a) =>
         MayHaveMonoidalField name a (x :*: y) where
   getMonoidalField name (x :*: y) = getMonoidalField name x <> getMonoidalField name y

instance TypeError (Text "Cannot get a single field value from a sum type") =>
         MayHaveMonoidalField name a (x :+: y) where
   getMonoidalField _ _ = error "getMonoidalField on sum type"

instance MayHaveMonoidalField name a (M1 i ('MetaSel ('Just name) su ss ds) (K1 j a)) where
   getMonoidalField name (M1 (K1 v)) = v

instance Monoid a => MayHaveMonoidalField name a f where
   getMonoidalField name _ = mempty

instance (Synthesizer' t g deep shallow x, Synthesizer' t g deep shallow y) =>
         Synthesizer' t g deep shallow (x :*: y) where
   synthesis' t node i s = synthesis' t node i s :*: synthesis' t node i s

instance SynthesizerField' t g deep shallow name f =>
         Synthesizer' t g deep shallow (M1 i ('MetaSel ('Just name) su ss ds) f) where
   synthesis' t node i s = M1 (synthesisF' t node i s (Proxy :: Proxy name))

instance SynthesizerField t g deep shallow name a => SynthesizerField' t g deep shallow name (K1 i a) where
   synthesisF' t node i s name = K1 (synthesisF t node i s name)

instance  {-# overlappable #-} (Monoid a, Shallow.Foldable (Accumulator t name a) (g (Semantics t))) =>
                               SynthesizerField t g deep shallow name (Accumulated a) where
   synthesisF t _ _ s name = Accumulated (Shallow.foldMap (Accumulator :: Accumulator t name a) s)

instance  {-# overlappable #-} (Applicative m, a ~ g (Semantics t) n,
                                Shallow.Traversable (Replicator t m n name a) (g (Semantics t))) =>
                               SynthesizerField t g deep shallow name (Replicated m n a) where
   synthesisF t _ _ s name = Replicated (Shallow.traverse (Replicator :: Replicator t m n name a) s)

bequestDefault, passDown :: forall sem shallow t g.
                            (sem ~ Semantics t, Domain t ~ shallow, Revelation t,
                             Shallow.Functor (PassDown t sem (Atts (Inherited t) (g sem sem))) (g sem))
                         => t -> shallow (g sem sem)
                         -> Atts (Inherited t) (g sem sem)
                         -> g sem (Synthesized t)
                         -> g sem (Inherited t)
bequestDefault t local inheritance synthesized = PassDown inheritance Shallow.<$> reveal t local
passDown = bequestDefault
