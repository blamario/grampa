{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa.Types (Functor1(..), Foldable1(..), Traversable1(..), Reassemblable(..),
                          Grammar, GrammarBuilder, Parser(..), Production,
                          feed, feedEnd, feedGrammar, fixGrammar, iterateMany, results)
where

import Control.Applicative
import Data.Function(fix)
import Data.Monoid (Monoid, mappend, mempty, (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(spanMaybe', splitPrimePrefix, tails))

import Prelude hiding (null)

class Functor1 g where
   fmap1 :: (forall a. p a -> q a) -> g p -> g q

class Functor1 g => Foldable1 g where
   foldMap1 :: Monoid m => (forall a. p a -> m) -> g p -> m

class Foldable1 g => Traversable1 g where
   traverse1 :: Applicative m => (forall a. p a -> m (q a)) -> g p -> m (g q)

class Functor1 g => Reassemblable g where
   applyFieldwise :: (g p -> g p) -> g p -> g p -> g p
   reassemble :: (forall a. (g p -> p a) -> (p a -> g p) -> g p -> q a) -> g p -> g q

data Parser g s r = Failure String
                  | Result [(Grammar g s, s)] r
                  | Choice (Parser g s r) (Parser g s r)
                  | Delay (Parser g s r) ([(Grammar g s, s)] -> Parser g s r)
                  | Recursive (Parser g s r)

type Grammar g s = g (Parser g s)
type GrammarBuilder g g' s = g (Parser g' s) -> g (Parser g' s)
type Production g p r = g p -> p r

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
   
fixGrammar :: (MonoidNull s, Reassemblable g) => (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar gf = tieRecursion (fix $ gf' . reassemble nt)
   where gf' g = applyFieldwise gf (fmap1 Recursive g) g

fixGrammar' :: Reassemblable g => (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar' = fix . (. reassemble nt)

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

feedGrammar :: (FactorialMonoid s, Functor1 g) => Grammar g s -> s -> Grammar g s -> Grammar g s
feedGrammar g s = fmap1 (feed $ fixGrammarInput g s)

fixGrammarInput :: (FactorialMonoid s, Functor1 g) => Grammar g s -> s -> [(Grammar g s, s)]
fixGrammarInput parsers s = foldr parseTail [] (tails s)
   where parseTail input parsedTail = parsedInput
            where parsedInput = (fmap1 (feed parsedInput) parsers, input):parsedTail

nt :: (Grammar g s -> Parser g s r) -> (Parser g s r -> Grammar g s) -> Grammar g s -> Parser g s r
nt f _ g = Delay (f g) (\((t, _):_)-> f t)

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

feedEnd :: (MonoidNull s, Functor1 g) => Parser g s r -> Parser g s r
feedEnd (Choice p q) = feedEnd p <|> feedEnd q
feedEnd (Delay e _) = feedEnd e
feedEnd (Recursive p) = Recursive (feedEnd p)
feedEnd p = p

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

iterateMany :: (MonoidNull s, Functor1 g) => Parser g s r -> (Parser g s r -> Parser g s r) -> Parser g s r
iterateMany p f = p >>= (\r-> return r <|> iterateMany (f $ return r) f)
