{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, KindSignatures,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa.Types (Functor1(..), Apply1(..), Alternative1(..), Foldable1(..), Traversable1(..),
                          Reassemblable(..),
                          Grammar, GrammarBuilder, Parser(..), Production, Identity1(..), Product1(..), Arrow1(..),
                          feed, feedEnd, feedGrammar, fixGrammar, iterateMany, production, results)
where

import Control.Applicative
import Data.Function(fix)
import Data.Monoid (Monoid, mappend, mempty, (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(spanMaybe', splitPrimePrefix, tails))

import Prelude hiding (null)

-- | Equivalent of 'Functor' for rank 2 data types
class Functor1 g where
   fmap1 :: (forall a. p a -> q a) -> g p -> g q

-- | Equivalent of 'Foldable' for rank 2 data types
class Functor1 g => Foldable1 g where
   foldMap1 :: Monoid m => (forall a. p a -> m) -> g p -> m

-- | Equivalent of 'Traversable' for rank 2 data types
class Foldable1 g => Traversable1 g where
   traverse1 :: Applicative m => (forall a. p a -> m (q a)) -> g p -> m (g q)

data Arrow1 p q a = Arrow1{apply1 :: p a -> q a}

-- | Equivalent of 'Applicative' with no 'pure' method, for rank 2 data types
--
-- > (.) <$> u <*> v <*> w == u <*> (v <*> w)
class Functor1 g => Apply1 g where
   ap1 :: g (Arrow1 p q) -> g p -> g q

-- | Equivalent of 'Applicative' with no 'pure' method, for rank 2 data types
--
-- > choose1 empty1 x == x
-- > choose1 x empty1 == x
-- > x `choose1` (y `choose1` z) == (x `choose1` y) `choose1` z
-- > ap1 empty x == empty
-- > ap1 x (choose1 y z) == choose1 (ap1 x y) (ap1 x z)
-- > ap1 (choose1 x y) z == choose1 (ap1 x z) (ap1 y z)
class Apply1 g => Alternative1 g where
   empty1 :: Alternative p => g p
   choose1 :: Alternative p => g p -> g p -> g p

-- | Subclass of 'Functor' that allows access to parts of the data structure
class Functor1 g => Reassemblable g where
   applyFieldwise :: (g p -> g p) -> g p -> g p -> g p
   reassemble :: (forall a. (g p -> p a) -> (p a -> g p) -> g p -> q a) -> g p -> g q

-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
data Parser g s r = Failure String
                  | Result [(Grammar g s, s)] r
                  | Choice (Parser g s r) (Parser g s r)
                  | Delay (Parser g s r) ([(Grammar g s, s)] -> Parser g s r)
                  | Recursive (Parser g s r)

-- | Equivalent of 'Data.Functor.Identity' for rank 2 data types
data Identity1 g (f :: * -> *) = Identity1 {runIdentity1 :: g f} deriving (Eq, Ord, Show)

-- | Equivalent of 'Data.Functor.Product' for rank 2 data types
data Product1 g h (f :: * -> *) = Pair {fst1 :: g f,
                                        snd1 :: h f}
                                deriving (Eq, Ord, Show)

type Grammar g s = g (Parser g s)
type GrammarBuilder g g' s = g (Parser g' s) -> g (Parser g' s)
type Production g s r = g (Parser g s) -> Parser g s r

instance (Show r, Show s, Show (Grammar g s)) => Show (Parser g s r) where
   showsPrec _ (Failure s) rest = "(Failure " ++ shows s (")" ++ rest)
   showsPrec prec (Result s r) rest
      | prec > 0 = "(Result " ++ foldr (\(t, s)-> showsPrec (prec - 1) t . shows s) (" " ++ shows r (")" ++ rest)) s
      | otherwise = "Result" ++ rest
   showsPrec prec (Choice p1 p2) rest = "(Choice " ++ showsPrec prec p1 (" " ++ showsPrec prec p2 (")" ++ rest))
   showsPrec prec (Recursive p) rest
      | prec > 0 = "(Recursive " ++ showsPrec (prec - 1) p (")" ++ rest)
      | otherwise = "Recursive" ++ rest
   showsPrec prec (Delay e f) rest = "(Delay " ++ showsPrec prec e (")" ++ rest)

instance Functor1 g => Functor1 (Identity1 g) where
   fmap1 f (Identity1 g) = Identity1 (fmap1 f g)

instance (Functor1 g, Functor1 h) => Functor1 (Product1 g h) where
   fmap1 f (Pair g h) = Pair (fmap1 f g) (fmap1 f h)

instance Foldable1 g => Foldable1 (Identity1 g) where
   foldMap1 f (Identity1 g) = foldMap1 f g

instance (Foldable1 g, Foldable1 h) => Foldable1 (Product1 g h) where
   foldMap1 f (Pair g h) = foldMap1 f g <> foldMap1 f h

instance Traversable1 g => Traversable1 (Identity1 g) where
   traverse1 f (Identity1 g) = Identity1 <$> traverse1 f g

instance (Traversable1 g, Traversable1 h) => Traversable1 (Product1 g h) where
   traverse1 f (Pair g h) = Pair <$> traverse1 f g <*> traverse1 f h

instance Apply1 g => Apply1 (Identity1 g) where
   ap1 (Identity1 g) (Identity1 h) = Identity1 (ap1 g h)

instance (Apply1 g, Apply1 h) => Apply1 (Product1 g h) where
   ap1 (Pair gf hf) (Pair g h) = Pair (ap1 gf g) (ap1 hf h)

instance Alternative1 g => Alternative1 (Identity1 g) where
   empty1 = Identity1 empty1
   choose1 (Identity1 g) (Identity1 h) = Identity1 (choose1 g h)

instance (Alternative1 g, Alternative1 h) => Alternative1 (Product1 g h) where
   empty1 = Pair empty1 empty1
   choose1 (Pair g1 h1) (Pair g2 h2) = Pair (choose1 g1 g2) (choose1 h1 h2)

instance Reassemblable g => Reassemblable (Identity1 g) where
   applyFieldwise f ~(Identity1 a) ~(Identity1 b) = Identity1 (applyFieldwise f' a b)
      where f' x = runIdentity1 (f $ Identity1 x)
   reassemble f ~(Identity1 a) = Identity1 (reassemble f' a)
      where f' get set x = f (get . runIdentity1) (\t->Identity1 $ set t) (Identity1 x)

instance (Reassemblable g, Reassemblable h) => Reassemblable (Product1 g h) where
   applyFieldwise f ~(Pair a b) ~(Pair c d) = Pair (applyFieldwise f' a c) (applyFieldwise f'' b d)
      where f' x = fst1 (f $ Pair x d)
            f'' x = snd1 (f $ Pair c x)
   reassemble f ~(Pair a b) = Pair (reassemble f' a) (reassemble f'' b)
      where f' get set x = f (get . fst1) (\t->Pair (set t) b) (Pair x b)
            f'' get set x = f (get . snd1) (\t->Pair a (set t)) (Pair a x)

-- | Tie the knot on a 'GrammarBuilder' and turn it into a 'Grammar'
fixGrammar :: (MonoidNull s, Reassemblable g) => (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar gf = tieRecursion (fix $ gf' . reassemble (const . production id))
   where gf' g = applyFieldwise gf (fmap1 Recursive g) g

fixGrammar' :: Reassemblable g => (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar' = fix . (. reassemble (const . production id))

tieRecursion :: (MonoidNull s, Reassemblable g) => Grammar g s -> Grammar g s
tieRecursion = reassemble tie

tie :: (MonoidNull s, Functor1 g) =>
        (Grammar g s -> Parser g s r)
     -> (Parser g s r -> Grammar g s)
     -> Grammar g s
     -> Parser g s r
tie get set g = case separate (get g)
                of (p, Failure{}) -> p
                   (Failure{}, _) -> Failure "Unlimited left recursion"
                   (nonRecursive, recursive) -> iterateMany nonRecursive (\p-> feed [(set p, mempty)] recursive)
   where separate (Choice p q) = (pn <|> qn, pr <|> qr)
            where (pn, pr) = separate p
                  (qn, qr) = separate q
         separate (Recursive p) = (empty, p)
         separate p = (p, empty)

-- | Feeds a chunk of the input `s` to the given grammar.
feedGrammar :: (FactorialMonoid s, Functor1 g) => Grammar g s -> s -> Grammar g s -> Grammar g s
feedGrammar g s = fmap1 (feed $ fixGrammarInput g s)

fixGrammarInput :: (FactorialMonoid s, Functor1 g) => Grammar g s -> s -> [(Grammar g s, s)]
fixGrammarInput parsers s = foldr parseTail [] (tails s)
   where parseTail input parsedTail = parsedInput
            where parsedInput = (fmap1 (feed parsedInput) parsers, input):parsedTail

production :: (g' (Parser g' s) -> g (Parser g' s)) -> (g (Parser g' s) -> Parser g' s r) -> g (Parser g' s)
           -> Parser g' s r
production sub prod g = Delay (prod g) (\((g', _):_)-> prod $ sub g')

-- | Feeds a chunk of the input to the given parser.
feed :: (MonoidNull s, Functor1 g) => [(Grammar g s, s)] -> Parser g s r -> Parser g s r
feed [] p = p
feed s (Choice p q) = feed s p <|> feed s q
feed s (Delay _ f) = f s
feed s (Failure msg) = Failure msg
feed s (Result t r) = Result (foldr refeed s t) r
   where refeed (t, s') rest
            | null s' = rest
            | otherwise = (fmap1 (feed s) t, s' <> s''):rest
         s'' = snd (head s)
feed s (Recursive p) = feed s p

-- | Signals the end of the input.
feedEnd :: (MonoidNull s, Functor1 g) => Parser g s r -> Parser g s r
feedEnd (Choice p q) = feedEnd p <|> feedEnd q
feedEnd (Delay e _) = feedEnd e
feedEnd (Recursive p) = Recursive (feedEnd p)
feedEnd p = p

-- | Extracts all available parsing results from a 'Parser'.
results :: (FactorialMonoid s, Functor1 g) => Parser g s r -> [(r, [(Grammar g s, s)])]
results Failure{} = []
results (Result s r) = [(r, s)]
results (Choice p q) = results p <> results q
results (Delay e _) = results e

instance Functor (Parser g s) where
   fmap f (Choice p q) = Choice (fmap f p) (fmap f q)
   fmap g (Delay e f) = Delay (fmap g e) (fmap g . f)
   fmap f (Failure msg) = Failure msg
   fmap f (Result s r) = Result s (f r)
   fmap f (Recursive p) = Recursive (fmap f p)

instance (MonoidNull s, Functor1 g) => Applicative (Parser g s) where
   pure = Result []
   Choice p q <*> r = p <*> r <|> q <*> r
   Delay e f <*> p = Delay (e <*> p) ((<*> p) . f)
   Failure msg <*> _ = Failure msg
   Result s r <*> p = r <$> feed s p
   Recursive p <*> q = Recursive (p <*> q)

instance (MonoidNull s, Functor1 g) => Alternative (Parser g s) where
   empty = Failure "empty"
   p <|> Failure{} = p
   Failure{} <|> p = p
--   Delay e f <|> p = Delay (e <|> feedEnd p) (\i-> f i <|> feed i p)
--   p <|> Delay e f = Delay (feedEnd p <|> e) (\i-> feed i p <|> f i)
   p <|> q = Choice p q

instance (MonoidNull s, Functor1 g) => Monad (Parser g s) where
   return = pure
   Result s r >>= f = feed s (f r)
   Choice p q >>= f = (p >>= f) <|> (q >>= f)
   Delay e f >>= g = Delay (e >>= g) ((>>= g) . f)
   Failure msg >>= f = Failure msg
   Recursive p >>= f = Recursive (p >>= f)
   (>>) = (*>)
   fail = Failure

instance (Functor1 g, MonoidNull s, Monoid x) => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

iterateMany :: (MonoidNull s, Functor1 g) => Parser g s r -> (Parser g s r -> Parser g s r) -> Parser g s r
iterateMany p f = p >>= (\r-> return r <|> iterateMany (f $ return r) f)
