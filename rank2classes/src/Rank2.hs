-- | Import this module qualified, like this:
-- 
-- > import qualified Rank2
-- 
-- This will bring into scope the standard classes 'Functor', 'Applicative', 'Foldable', and 'Traversable', but with a
-- @Rank2.@ prefix and a twist that their methods operate on a heterogenous collection. The same property is shared by
-- the less standard classes 'Apply', 'Distributive', and 'Logistic'.
{-# LANGUAGE DefaultSignatures, InstanceSigs, KindSignatures, PolyKinds, Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeOperators, UndecidableInstances #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeApplications #-}
module Rank2 (
-- * Rank 2 classes
   Functor(..), Apply(..), Applicative(..),
   Foldable(..), Traversable(..), Distributive(..), DistributiveTraversable(..), Logistic(..), distributeJoin,
-- * Rank 2 data types
   Compose(..), Empty(..), Only(..), Flip(..), Identity(..), Product(..), Sum(..), Arrow(..), type (~>),
-- * Method synonyms and helper functions
   ($), fst, snd, ap, fmap, liftA4, liftA5,
   fmapTraverse, liftA2Traverse1, liftA2Traverse2, liftA2TraverseBoth,
   distributeWith, distributeWithTraversable,
   getters, setters)
where

import qualified Control.Applicative as Rank1
import qualified Control.Monad as Rank1
import qualified Data.Foldable as Rank1
import qualified Data.Traversable as Rank1
import qualified Data.Functor.Compose as Rank1
import qualified Data.Functor.Contravariant as Rank1
import qualified Data.Functor.Logistic as Rank1
import qualified Data.Distributive as Rank1
import Data.Coerce (coerce)
import Data.Semigroup (Semigroup(..))
import Data.Monoid (Monoid(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Product (Product(Pair))
import Data.Functor.Sum (Sum(InL, InR))
import Data.Kind (Type)
import Data.Proxy (Proxy(..))
import qualified GHC.Generics as Generics

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), ($), (<$>), fst, snd)

-- | Helper function for accessing the first field of a 'Pair'
fst :: Product g h p -> g p
fst (Pair x _) = x

-- | Helper function for accessing the second field of a 'Pair'
snd :: Product g h p -> h p
snd (Pair _ y) = y

-- | Equivalent of 'Rank1.Functor' for rank 2 data types, satisfying the usual functor laws
--
-- > id <$> g == g
-- > (p . q) <$> g == p <$> (q <$> g)
class Functor g where
   (<$>) :: (forall a. p a -> q a) -> g p -> g q
infixl 4 <$>

-- | Alphabetical synonym for '<$>'
fmap :: Functor g => (forall a. p a -> q a) -> g p -> g q
fmap f g = f <$> g
{-# INLINE fmap #-}

-- | Equivalent of 'Rank1.Foldable' for rank 2 data types
class Foldable g where
   foldMap :: Monoid m => (forall a. p a -> m) -> g p -> m

-- | Equivalent of 'Rank1.Traversable' for rank 2 data types
class (Functor g, Foldable g) => Traversable g where
   {-# MINIMAL traverse | sequence #-}
   traverse :: Rank1.Applicative m => (forall a. p a -> m (q a)) -> g p -> m (g q)
   sequence :: Rank1.Applicative m => g (Rank1.Compose m p) -> m (g p)
   traverse f = sequence . fmap (Rank1.Compose . f)
   sequence = traverse Rank1.getCompose
-- | Wrapper for functions that map the argument constructor type
newtype Arrow p q a = Arrow{apply :: p a -> q a}

type (~>) = Arrow
($) :: Arrow p q a -> p a -> q a
($) = apply
infixr 0 ~>
infixr 0 $

-- | Subclass of 'Functor' halfway to 'Applicative', satisfying
--
-- > (.) <$> u <*> v <*> w == u <*> (v <*> w)
class Functor g => Apply g where
   {-# MINIMAL liftA2 | (<*>) #-}
   -- | Equivalent of 'Rank1.<*>' for rank 2 data types
   (<*>) :: g (p ~> q) -> g p -> g q
   -- | Equivalent of 'Rank1.liftA2' for rank 2 data types
   liftA2 :: (forall a. p a -> q a -> r a) -> g p -> g q -> g r
   -- | Equivalent of 'Rank1.liftA3' for rank 2 data types
   liftA3 :: (forall a. p a -> q a -> r a -> s a) -> g p -> g q -> g r -> g s

   (<*>) = liftA2 apply
   liftA2 f g h = (Arrow . f) <$> g <*> h
   liftA3 f g h i = liftA2 (\p q-> Arrow (f p q)) g h <*> i
infixl 4 <*>

liftA4 :: Apply g => (forall a. p a -> q a -> r a -> s a -> t a) -> g p -> g q -> g r -> g s -> g t
liftA4 f g h i j = liftA3 (\p q r-> Arrow (f p q r)) g h i <*> j

liftA5 :: Apply g => (forall a. p a -> q a -> r a -> s a -> t a -> u a) -> g p -> g q -> g r -> g s -> g t -> g u
liftA5 f g1 g2 g3 g4 g5 = liftA4 (\p q r s-> Arrow (f p q r s)) g1 g2 g3 g4 <*> g5

-- | Alphabetical synonym for '<*>'
ap :: Apply g => g (p ~> q) -> g p -> g q
ap = (<*>)

-- | Equivalent of 'Rank1.Applicative' for rank 2 data types
class Apply g => Applicative g where
   pure :: (forall a. f a) -> g f

-- | Equivalent of 'Rank1.Distributive' for rank 2 data types
class DistributiveTraversable g => Distributive g where
   {-# MINIMAL cotraverse|distribute #-}
   collect :: Rank1.Functor p => (a -> g q) -> p a -> g (Rank1.Compose p q)
   distribute :: Rank1.Functor p => p (g q) -> g (Rank1.Compose p q)
   -- | Dual of 'traverse', equivalent of 'Rank1.cotraverse' for rank 2 data types 
   cotraverse :: Rank1.Functor m => (forall a. m (p a) -> q a) -> m (g p) -> g q

   collect f = distribute . Rank1.fmap f
   distribute = cotraverse Rank1.Compose
   cotraverse f = fmap (f . Rank1.getCompose) . distribute

-- | A weaker 'Distributive' that requires 'Rank1.Traversable' to use, not just a 'Rank1.Functor'.
class Functor g => DistributiveTraversable (g :: (k -> Type) -> Type) where
   collectTraversable :: Rank1.Traversable f1 => (a -> g f2) -> f1 a -> g (Rank1.Compose f1 f2)   
   distributeTraversable :: Rank1.Traversable f1 => f1 (g f2) -> g (Rank1.Compose f1 f2)
   cotraverseTraversable :: Rank1.Traversable f1 => (forall x. f1 (f2 x) -> f x) -> f1 (g f2) -> g f

   collectTraversable f = distributeTraversable . Rank1.fmap f
   distributeTraversable = cotraverseTraversable Rank1.Compose
   
   default cotraverseTraversable :: (Rank1.Traversable m, Distributive g) => 
                                    (forall a. m (p a) -> q a) -> m (g p) -> g q
   cotraverseTraversable = cotraverse

-- | Equivalent of 'Rank1.Logistic' for rank 2 data types
class Functor g => Logistic g where
   deliver :: Rank1.Contravariant p => p (g q -> g q) -> g (Rank1.Compose p (q ~> q))

-- | A variant of 'distribute' convenient with 'Rank1.Monad' instances
distributeJoin :: (Distributive g, Rank1.Monad f) => f (g f) -> g f
distributeJoin = cotraverse Rank1.join

-- | Like 'fmap', but traverses over its argument
fmapTraverse :: (DistributiveTraversable g, Rank1.Traversable f) => (forall a. f (t a) -> u a) -> f (g t) -> g u
fmapTraverse f x = fmap (f . Rank1.getCompose) (distributeTraversable x)

-- | Like 'liftA2', but traverses over its first argument
liftA2Traverse1 :: (Apply g, DistributiveTraversable g, Rank1.Traversable f) =>
                   (forall a. f (t a) -> u a -> v a) -> f (g t) -> g u -> g v
liftA2Traverse1 f x = liftA2 (f . Rank1.getCompose) (distributeTraversable x)

-- | Like 'liftA2', but traverses over its second argument
liftA2Traverse2 :: (Apply g, DistributiveTraversable g, Rank1.Traversable f) => 
                   (forall a. t a -> f (u a) -> v a) -> g t -> f (g u) -> g v
liftA2Traverse2 f x y = liftA2 (\x' y' -> f x' (Rank1.getCompose y')) x (distributeTraversable y)

-- | Like 'liftA2', but traverses over both its arguments
liftA2TraverseBoth :: forall f1 f2 g t u v.
                      (Apply g, DistributiveTraversable g, Rank1.Traversable f1, Rank1.Traversable f2) =>
                      (forall a. f1 (t a) -> f2 (u a) -> v a) -> f1 (g t) -> f2 (g u) -> g v
liftA2TraverseBoth f x y = liftA2 applyCompose (distributeTraversable x) (distributeTraversable y)
   where applyCompose :: forall a. Rank1.Compose f1 t a -> Rank1.Compose f2 u a -> v a
         applyCompose x' y' = f (Rank1.getCompose x') (Rank1.getCompose y')

-- | Enumerate getters for each element
getters :: Distributive g => g (Rank1.Compose ((->) (g f)) f)
getters = distribute id

-- | Enumerate setters for each element
setters :: Logistic g => g ((f ~> f) ~> Const (g f -> g f))
setters = Arrow . (Const .) . Rank1.getOp . Rank1.getCompose <$> deliver (Rank1.Op id)

{-# DEPRECATED distributeWith "Use cotraverse instead." #-}
-- | Synonym for 'cotraverse'
distributeWith :: (Distributive g, Rank1.Functor f) => (forall i. f (a i) -> b i) -> f (g a) -> g b
distributeWith = cotraverse

{-# DEPRECATED distributeWithTraversable "Use cotraverseTraversable instead." #-}
-- | Synonym for 'cotraverseTraversable'
distributeWithTraversable :: (DistributiveTraversable g, Rank1.Traversable m) =>
                             (forall a. m (p a) -> q a) -> m (g p) -> g q
distributeWithTraversable = cotraverseTraversable

-- | A rank-2 equivalent of @()@, a zero-element tuple
data Empty f = Empty deriving (Eq, Ord, Show)

-- | A rank-2 tuple of only one element
newtype Only a f = Only {fromOnly :: f a} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Identity' for rank 2 data types
newtype Identity g f = Identity {runIdentity :: g f} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Compose' for rank 2 data types
newtype Compose g p q = Compose {getCompose :: g (Rank1.Compose p q)}

deriving instance Eq (g (Rank1.Compose p q)) => Eq (Compose g p q)
deriving instance Ord (g (Rank1.Compose p q)) => Ord (Compose g p q)
deriving instance Show (g (Rank1.Compose p q)) => Show (Compose g p q)

-- | A nested parametric type represented as a rank-2 type
newtype Flip g a f = Flip {unFlip :: g (f a)} deriving (Eq, Ord, Show)

instance Semigroup (g (f a)) => Semigroup (Flip g a f) where
   Flip x <> Flip y = Flip (x <> y)

instance Monoid (g (f a)) => Monoid (Flip g a f) where
   mempty = Flip mempty
   mappend = (<>)

instance Rank1.Functor g => Rank2.Functor (Flip g a) where
   f <$> Flip g = Flip (f Rank1.<$> g)

instance Rank1.Applicative g => Rank2.Apply (Flip g a) where
   Flip g <*> Flip h = Flip (apply Rank1.<$> g Rank1.<*> h)

instance Rank1.Applicative g => Rank2.Applicative (Flip g a) where
   pure f = Flip (Rank1.pure f)

instance Rank1.Foldable g => Rank2.Foldable (Flip g a) where
   foldMap f (Flip g) = Rank1.foldMap f g

instance Rank1.Traversable g => Rank2.Traversable (Flip g a) where
   traverse f (Flip g) = Flip Rank1.<$> Rank1.traverse f g

instance Functor Empty where
   _ <$> _ = Empty

instance Functor Proxy where
   _ <$> _ = Proxy

instance Functor (Const a) where
   _ <$> Const a = Const a

instance Functor (Only a) where
   f <$> Only a = Only (f a)

instance Functor g => Functor (Identity g) where
   f <$> Identity g = Identity (f <$> g)

instance (Functor g, Rank1.Functor p) => Functor (Compose g p) where
   (<$>) :: forall q r. (forall a. q a -> r a) -> Compose g p q -> Compose g p r
   f <$> Compose g = Compose (f' <$> g)
      where f' :: forall a. Rank1.Compose p q a -> Rank1.Compose p r a
            f' (Rank1.Compose q) = Rank1.Compose (f Rank1.<$> q)

instance (Functor g, Functor h) => Functor (Product g h) where
   f <$> Pair a b = Pair (f <$> a) (f <$> b)

instance (Functor g, Functor h) => Functor (Sum g h) where
   f <$> InL g = InL (f <$> g)
   f <$> InR h = InR (f <$> h)

instance Functor Generics.V1 where
   (<$>) _ = coerce
   
instance Functor Generics.U1 where
   (<$>) _ = coerce

instance Functor (Generics.K1 i c) where
   (<$>) _ = coerce

instance Functor f => Functor (Generics.M1 i c f) where
   f <$> Generics.M1 x = Generics.M1 (f <$> x)

instance Functor f => Functor (Generics.Rec1 f) where
   f <$> Generics.Rec1 x = Generics.Rec1 (f <$> x)

-- instance (Rank1.Functor f, Functor g) => Functor ((Generics.:.:) f g) where
--    f <$> Generics.Comp1 x = Generics.Comp1 (Rank1.fmap (f <$>) x)

instance (Functor f, Functor g) => Functor ((Generics.:+:) f g) where
   f <$> Generics.L1 x = Generics.L1 (f <$> x)
   f <$> Generics.R1 x = Generics.R1 (f <$> x)

instance (Functor f, Functor g) => Functor ((Generics.:*:) f g) where
   f <$> (x Generics.:*: y) = (f <$> x) Generics.:*: (f <$> y)

instance Foldable Empty where
   foldMap _ _ = mempty

instance Foldable Proxy where
   foldMap _ _ = mempty

instance Foldable (Const x) where
   foldMap _ _ = mempty

instance Foldable (Only x) where
   foldMap f (Only x) = f x

instance Foldable g => Foldable (Identity g) where
   foldMap f (Identity g) = foldMap f g

instance (Foldable g, Rank1.Foldable p) => Foldable (Compose g p) where
   foldMap f (Compose g) = foldMap (Rank1.foldMap f . Rank1.getCompose) g

instance (Foldable g, Foldable h) => Foldable (Product g h) where
   foldMap f (Pair g h) = foldMap f g `mappend` foldMap f h

instance (Foldable g, Foldable h) => Foldable (Sum g h) where
   foldMap f (InL g) = foldMap f g
   foldMap f (InR h) = foldMap f h

instance Foldable Generics.V1 where
   foldMap _ v = case v of {}
   
instance Foldable Generics.U1 where
   foldMap _ _ = mempty

instance Foldable (Generics.K1 i c) where
   foldMap _ _ = mempty

instance Foldable f => Foldable (Generics.M1 i c f) where
   foldMap f (Generics.M1 x) = foldMap f x

instance Foldable f => Foldable (Generics.Rec1 f) where
   foldMap f (Generics.Rec1 x) = foldMap f x

instance (Foldable f, Foldable g) => Foldable ((Generics.:+:) f g) where
   foldMap f (Generics.L1 x) = foldMap f x
   foldMap f (Generics.R1 x) = foldMap f x

instance (Foldable f, Foldable g) => Foldable ((Generics.:*:) f g) where
   foldMap f (x Generics.:*: y) = foldMap f x `mappend` foldMap f y

instance Traversable Empty where
   traverse _ _ = Rank1.pure Empty

instance Traversable Proxy where
   traverse _ _ = Rank1.pure Proxy

instance Traversable (Const x) where
   traverse _ (Const x) = Rank1.pure (Const x)

instance Traversable (Only x) where
   traverse f (Only x) = Only Rank1.<$> f x

instance Traversable g => Traversable (Identity g) where
   traverse f (Identity g) = Identity Rank1.<$> traverse f g

instance (Traversable g, Rank1.Traversable p) => Traversable (Compose g p) where
   traverse :: forall m q r. Rank1.Applicative m => (forall a. q a -> m (r a)) -> Compose g p q -> m (Compose g p r)
   traverse f (Compose g) = Compose Rank1.<$> traverse f' g
      where f' :: forall a. Rank1.Compose p q a -> m (Rank1.Compose p r a)
            f' (Rank1.Compose q) = Rank1.Compose Rank1.<$> Rank1.traverse f q

instance (Traversable g, Traversable h) => Traversable (Product g h) where
   traverse f (Pair g h) = Rank1.liftA2 Pair (traverse f g) (traverse f h)

instance (Traversable g, Traversable h) => Traversable (Sum g h) where
   traverse f (InL g) = InL Rank1.<$> traverse f g
   traverse f (InR h) = InR Rank1.<$> traverse f h

instance Traversable Generics.V1 where
   traverse _ = Rank1.pure . coerce
   
instance Traversable Generics.U1 where
   traverse _ = Rank1.pure . coerce

instance Traversable (Generics.K1 i c) where
   traverse _ = Rank1.pure . coerce

instance Traversable f => Traversable (Generics.M1 i c f) where
   traverse f (Generics.M1 x) = Rank1.fmap Generics.M1 (traverse f x)

instance Traversable f => Traversable (Generics.Rec1 f) where
   traverse f (Generics.Rec1 x) = Rank1.fmap Generics.Rec1 (traverse f x)

instance (Traversable f, Traversable g) => Traversable ((Generics.:+:) f g) where
   traverse f (Generics.L1 x) = Rank1.fmap Generics.L1 (traverse f x)
   traverse f (Generics.R1 x) = Rank1.fmap Generics.R1 (traverse f x)

instance (Traversable f, Traversable g) => Traversable ((Generics.:*:) f g) where
   traverse f (x Generics.:*: y) = Rank1.liftA2 (Generics.:*:) (traverse f x) (traverse f y)

instance Apply Empty where
   _ <*> _ = Empty
   liftA2 _ _ _ = Empty

instance Apply Proxy where
   _ <*> _ = Proxy
   liftA2 _ _ _ = Proxy

instance Semigroup x => Apply (Const x) where
   Const x <*> Const y = Const (x <> y)
   liftA2 _ (Const x) (Const y) = Const (x <> y)

instance Apply (Only x) where
   Only f <*> Only x = Only (apply f x)
   liftA2 f (Only x) (Only y) = Only (f x y)

instance Apply g => Apply (Identity g) where
   Identity g <*> Identity h = Identity (g <*> h)
   liftA2 f (Identity g) (Identity h) = Identity (liftA2 f g h)

instance (Apply g, Rank1.Applicative p) => Apply (Compose g p) where
   (<*>)  :: forall q r. Compose g p (q ~> r) -> Compose g p q -> Compose g p r
   liftA2 :: forall q r s. (forall a. q a -> r a -> s a) -> Compose g p q -> Compose g p r -> Compose g p s
   Compose g <*> Compose h = Compose (liftA2 f' g h)
      where f' :: forall a. Rank1.Compose p (q ~> r) a -> Rank1.Compose p q a -> Rank1.Compose p r a
            f' (Rank1.Compose f) (Rank1.Compose q) = Rank1.Compose (Rank1.liftA2 apply f q)
   liftA2 f (Compose g) (Compose h) = Compose (liftA2 f' g h)
      where f' :: forall a. Rank1.Compose p q a -> Rank1.Compose p r a -> Rank1.Compose p s a
            f' (Rank1.Compose q) (Rank1.Compose r) = Rank1.Compose (Rank1.liftA2 f q r)

instance (Apply g, Apply h) => Apply (Product g h) where
   Pair gf hf <*> ~(Pair gx hx) = Pair (gf <*> gx) (hf <*> hx)
   liftA2 f (Pair g1 h1) ~(Pair g2 h2) = Pair (liftA2 f g1 g2) (liftA2 f h1 h2)
   liftA3 f (Pair g1 h1) ~(Pair g2 h2) ~(Pair g3 h3) = Pair (liftA3 f g1 g2 g3) (liftA3 f h1 h2 h3)

instance Apply Generics.V1 where
   (<*>) _ = coerce
   
instance Apply Generics.U1 where
   (<*>) _ = coerce

instance Semigroup c => Apply (Generics.K1 i c) where
   Generics.K1 x <*> Generics.K1 y = Generics.K1 (x <> y)

instance Apply f => Apply (Generics.M1 i c f) where
   Generics.M1 f <*> Generics.M1 x = Generics.M1 (f <*> x)

instance Apply f => Apply (Generics.Rec1 f) where
   Generics.Rec1 f <*> Generics.Rec1 x = Generics.Rec1 (f <*> x)

instance (Apply f, Apply g) => Apply ((Generics.:*:) f g) where
   (x1 Generics.:*: y1) <*> (x2 Generics.:*: y2) = (x1 <*> x2) Generics.:*: (y1 <*> y2)

instance Applicative Empty where
   pure _ = Empty

instance Applicative Proxy where
   pure _ = Proxy

instance (Semigroup x, Monoid x) => Applicative (Const x) where
   pure _ = Const mempty

instance Applicative (Only x) where
   pure f = Only f

instance Applicative g => Applicative (Identity g) where
   pure f = Identity (pure f)

instance (Applicative g, Rank1.Applicative p) => Applicative (Compose g p) where
   pure f = Compose (pure (Rank1.Compose (Rank1.pure f)))

instance (Applicative g, Applicative h) => Applicative (Product g h) where
   pure f = Pair (pure f) (pure f)

instance (Semigroup c, Monoid c) => Applicative (Generics.K1 i c) where
   pure _ = Generics.K1 mempty

instance Applicative f => Applicative (Generics.M1 i c f) where
   pure f = Generics.M1 (pure f)

instance Applicative f => Applicative (Generics.Rec1 f) where
   pure f = Generics.Rec1 (pure f)

instance (Applicative f, Applicative g) => Applicative ((Generics.:*:) f g) where
   pure f = pure f Generics.:*: pure f
   
instance DistributiveTraversable Empty
instance DistributiveTraversable Proxy
instance DistributiveTraversable (Only x)
instance DistributiveTraversable g => DistributiveTraversable (Identity g) where
   cotraverseTraversable w f = Identity (cotraverseTraversable w (Rank1.fmap runIdentity f))
instance (DistributiveTraversable g, Rank1.Distributive p) => DistributiveTraversable (Compose g p) where
   cotraverseTraversable w f = Compose (cotraverseTraversable
                                        (Rank1.Compose . Rank1.fmap w . Rank1.distribute . Rank1.fmap Rank1.getCompose)
                                        (Rank1.fmap getCompose f))
instance (DistributiveTraversable g, DistributiveTraversable h) => DistributiveTraversable (Product g h) where
   cotraverseTraversable w f = Pair (cotraverseTraversable w (Rank1.fmap fst f))
                                    (cotraverseTraversable w (Rank1.fmap snd f))

instance DistributiveTraversable f => DistributiveTraversable (Generics.M1 i c f) where
   cotraverseTraversable w f = Generics.M1 (cotraverseTraversable w (Rank1.fmap Generics.unM1 f))
instance DistributiveTraversable f => DistributiveTraversable (Generics.Rec1 f) where
   cotraverseTraversable w f = Generics.Rec1 (cotraverseTraversable w (Rank1.fmap Generics.unRec1 f))
instance (DistributiveTraversable f, DistributiveTraversable g) => DistributiveTraversable ((Generics.:*:) f g) where
   cotraverseTraversable w f = cotraverseTraversable w (Rank1.fmap (\(a Generics.:*: _) -> a) f) Generics.:*: cotraverseTraversable w (Rank1.fmap (\(_ Generics.:*: b) -> b) f)

instance Distributive Empty where
   cotraverse _ _ = Empty

instance Distributive Proxy where
   cotraverse _ _ = Proxy

instance Monoid x => DistributiveTraversable (Const x) where
   cotraverseTraversable _ f = coerce (Rank1.fold f)

instance Distributive (Only x) where
   cotraverse w f = Only (w (Rank1.fmap fromOnly f))

instance Distributive g => Distributive (Identity g) where
   cotraverse w f = Identity (cotraverse w (Rank1.fmap runIdentity f))

instance (Distributive g, Rank1.Distributive p) => Distributive (Compose g p) where
   cotraverse w f = Compose (cotraverse (Rank1.Compose . Rank1.fmap w . Rank1.distribute . Rank1.fmap Rank1.getCompose)
                                        (Rank1.fmap getCompose f))

instance (Distributive g, Distributive h) => Distributive (Product g h) where
   cotraverse w f = Pair (cotraverse w (Rank1.fmap fst f)) (cotraverse w (Rank1.fmap snd f))

instance Monoid c => DistributiveTraversable (Generics.K1 i c) where
   cotraverseTraversable _ f = coerce (Rank1.foldMap Generics.unK1 f)

instance Distributive f => Distributive (Generics.M1 i c f) where
   cotraverse w f = Generics.M1 (cotraverse w (Rank1.fmap Generics.unM1 f))
instance Distributive f => Distributive (Generics.Rec1 f) where
   cotraverse w f = Generics.Rec1 (cotraverse w (Rank1.fmap Generics.unRec1 f))
instance (Distributive f, Distributive g) => Distributive ((Generics.:*:) f g) where
   cotraverse w f = cotraverse w (Rank1.fmap (\(a Generics.:*: _) -> a) f) Generics.:*: cotraverse w (Rank1.fmap (\(_ Generics.:*: b) -> b) f)

instance Logistic Empty where
   deliver _ = Empty

instance Logistic Proxy where
   deliver _ = Proxy

instance Logistic (Only x) where
   deliver f = Only (Rank1.Compose (Rank1.contramap coerce f))

instance Logistic g => Logistic (Identity g) where
   deliver f = Identity (deliver (Rank1.contramap coerce f))

instance (Logistic g, Rank1.Logistic p) => Logistic (Compose g p) where
   deliver = Compose
             . fmap (inRank1Compose (Rank1.fmap (Rank1.Compose . Rank1.contramap apply)
                                     . Rank1.deliver
                                     . Rank1.contramap (Arrow . inRank1Compose)))
             . deliver
             . Rank1.contramap inCompose

inCompose :: (g (Rank1.Compose p q) -> g' (Rank1.Compose p' q')) -> Compose g p q -> Compose g' p' q'
inCompose f = Compose . f . getCompose

inRank1Compose :: (p (q a) -> p' (q' a')) -> Rank1.Compose p q a -> Rank1.Compose p' q' a'
inRank1Compose f = Rank1.Compose . f . Rank1.getCompose

instance (Logistic g, Logistic h) => Logistic (Product g h) where
   deliver f = Pair (deliver (Rank1.contramap first f)) (deliver (Rank1.contramap second f))

first :: (g p -> g' p) -> Product g h p -> Product g' h p
first f (Pair g h) = Pair (f g) h

second :: (h p -> h' p) -> Product g h p -> Product g h' p
second f (Pair g h) = Pair g (f h)

instance Logistic f => Logistic (Generics.M1 i c f) where
   deliver f = Generics.M1 (deliver (Rank1.contramap (\f'-> Generics.M1 . f' . Generics.unM1) f))

instance Logistic f => Logistic (Generics.Rec1 f) where
   deliver f = Generics.Rec1 (deliver (Rank1.contramap (\f'-> Generics.Rec1 . f' . Generics.unRec1) f))

instance (Logistic f, Logistic g) => Logistic ((Generics.:*:) f g) where
   deliver f = deliver (Rank1.contramap (\f' (a Generics.:*: b) -> f' a Generics.:*: b) f)
               Generics.:*:
               deliver (Rank1.contramap (\f' (a Generics.:*: b) -> a Generics.:*: f' b) f)
