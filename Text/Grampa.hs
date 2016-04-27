{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa (Functor1(..), Foldable1(..), Traversable1(..), Reassemblable(..),
                    MonoidNull, FactorialMonoid, TextualMonoid,
                    Grammar, GrammarBuilder, Parser, Production,
                    feed, feedEnd, feedGrammar, fixGrammar, parse,
                    iterateMany, lookAhead, notFollowedBy,
                    endOfInput, anyToken, token, satisfy, satisfyChar, string,
                    scan, scanChars, takeWhile, takeWhile1, takeCharsWhile, takeCharsWhile1, skipCharsWhile)
where

import Control.Applicative
import Control.Arrow (second)
import Data.Function(fix)
import Data.Monoid (Monoid, mappend, mempty, (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid (stripPrefix))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(length, span, spanMaybe', splitPrimePrefix, tails))
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Textual as Textual
import Prelude hiding (length, null, span, takeWhile)

class Functor1 g where
   fmap1 :: (forall a. p a -> q a) -> g p -> g q

class Functor1 g => Foldable1 g where
   foldMap1 :: Monoid m => (forall a. p a -> m) -> g p -> m

class Foldable1 g => Traversable1 g where
   traverse1 :: Applicative m => (forall a. p a -> m (q a)) -> g p -> m (g q)

class Functor1 g => Reassemblable g where
   composePer :: (g p -> g p) -> (g p -> g p) -> (g p -> g p)
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
fixGrammar gf = tieRecursion $ fix (composePer gf (fmap1 $ Recursive) . reassemble nt)

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

parse :: (Reassemblable g, FactorialMonoid s) =>
         GrammarBuilder g g s -> (Production g (Parser g s) r) -> [s] -> [r]
parse g prod chunks = fst <$> results ((<* endOfInput) $ prod
                                      $ fmap1 feedEnd
                                      $ foldr (feedGrammar g') g'
                                      $ reverse chunks)
   where g' = fixGrammar g

results :: (FactorialMonoid s, Functor1 g) => Parser g s r -> [(r, [(Grammar g s, s)])]
results Failure{} = []
results (Result s r) = [(r, s)]
results (Choice p q) = results p <> results q
results (Delay e _) = results e
results (Recursive p) = findFixPoint Nothing 0 p
   where findFixPoint l d p = let r = resultsToDepth d p
                                  l' = Just $ minimum $ (length . inputWith . snd) <$> r
                              in if l == l'
                                 then r
                                 else findFixPoint l' (succ d) p

resultsToDepth :: (MonoidNull s, Functor1 g) => Int -> Parser g s r -> [(r, [(Grammar g s, s)])]
resultsToDepth _ Failure{} = []
resultsToDepth _ (Result s r) = [(r, s)]
resultsToDepth d (Choice p q) = resultsToDepth d p <> resultsToDepth d q
resultsToDepth d (Recursive p)
   | d > 0 = resultsToDepth (pred d) p
   | otherwise = []
resultsToDepth d (Delay e _) = resultsToDepth d e

resultPart :: (r -> r) -> Parser g s r -> Parser g s r
resultPart f p = f <$> p

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

-- | Behaves like the argument parser, but without consuming any input.
lookAhead :: (MonoidNull s, Functor1 g) => Parser g s r -> Parser g s r
lookAhead p = lookAheadInto [] p
   where -- lookAheadInto :: [(g (Parser g s), s)] -> Parser g s r -> Parser g s r
         lookAheadInto _ p@Failure{}        = p
         lookAheadInto t (Result _ r)       = Result t r
         lookAheadInto t (Choice p1 p2)     = lookAheadInto t p1 <|> lookAheadInto t p2
         lookAheadInto t (Delay e f)        = Delay (lookAheadInto t e) (\s-> lookAheadInto (mappend t s) (f s))

-- | Does not consume any input; succeeds (with 'mempty' result) iff the argument parser fails.
notFollowedBy :: (MonoidNull s, Functor1 g) => Parser g s r -> Parser g s ()
notFollowedBy = lookAheadNotInto []
   where -- lookAheadNotInto :: (Monoid s, Monoid r) => [(g (Parser g s), s)] -> Parser g s r -> Parser g s ()
         lookAheadNotInto t Failure{}   = Result t mempty
         lookAheadNotInto t Result{}   = Failure "notFollowedBy"
         lookAheadNotInto t (Delay e f) = Delay (lookAheadNotInto t e) (\s-> lookAheadNotInto (mappend t s) (f s))
         lookAheadNotInto t p = Delay (lookAheadNotInto t $ feedEnd p) (\s-> lookAheadNotInto (mappend t s) (feed s p))

-- | A parser that fails on any input and succeeds at its end
endOfInput :: (MonoidNull s, Functor1 g) => Parser g s ()
endOfInput = Delay (pure ()) (\s-> if null (inputWith s) then endOfInput else Failure "endOfInput")

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeWhile :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
takeWhile pred = while
   where while = Delay (pure mempty) f
         f i@((_, s):_) = let (prefix, suffix) = span pred s
                          in if null suffix then resultPart (mappend prefix) while
                             else Result (drop (length prefix) i) prefix

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
takeWhile1 pred = Delay (Failure "takeWhile1") f
   where f i@((_, s):_) | null s = takeWhile1 pred
                        | otherwise = let (prefix, suffix) = span pred s
                                      in if null prefix then Failure "takeWhile1"
                                         else if null suffix then resultPart (mappend prefix) (takeWhile pred)
                                              else Result (drop (length prefix) i) prefix

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeCharsWhile :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s s
takeCharsWhile pred = while
   where while = Delay (pure mempty) f
         f i@((_, s):_) = let (prefix, suffix) = Textual.span_ False pred s
                          in if null suffix then resultPart (mappend prefix) while
                             else Result (drop (length prefix) i) prefix

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s s
takeCharsWhile1 pred = Delay (Failure "takeCharsWhile1") f
   where f i@((_, s):_) | null s = takeCharsWhile1 pred
                        | otherwise = let (prefix, suffix) = Textual.span_ False pred s
                                      in if null prefix
                                         then Failure "takeCharsWhile1"
                                         else if null suffix then resultPart (mappend prefix) (takeCharsWhile pred)
                                              else Result (drop (length prefix) i) prefix

-- | A stateful scanner.  The predicate consumes and transforms a
-- state argument, and each transformed state is passed to successive invocations of the predicate on each token of the
-- input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first prime
-- input factor.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scan :: (FactorialMonoid t, Functor1 g) => s -> (s -> t -> Maybe s) -> Parser g t t
scan s0 f = Delay (pure mempty) (go s0)
 where go s i@((_, t):_) = let (prefix, suffix, s') = spanMaybe' s f t
                           in if null suffix then resultPart (mappend prefix) (scan s' f)
                              else Result (drop (length prefix) i) prefix

-- | A stateful scanner.  The predicate consumes and transforms a
-- state argument, and each transformed state is passed to successive invocations of the predicate on each token of the
-- input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first character.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scanChars :: (TextualMonoid t, Functor1 g) => s -> (s -> Char -> Maybe s) -> Parser g t t
scanChars s0 f = Delay (pure mempty) (go s0)
 where go s i@((_, t):_) = let (prefix, suffix, s') = Textual.spanMaybe_' s f t
                           in if null suffix then resultPart (mappend prefix) (scanChars s' f)
                              else Result (drop (length prefix) i) prefix

-- | A parser that accepts any single input atom.
anyToken :: (FactorialMonoid s, Functor1 g) => Parser g s s
anyToken = Delay (Failure "anyToken") f
   where f ((_, s):rest) = case splitPrimePrefix s
                           of Just (first, _) -> Result rest first
                              Nothing -> anyToken

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s, Functor1 g) => s -> Parser g s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
satisfy predicate = p
   where p = Delay (Failure "satisfy") f
         f ((_, s):rest) = case splitPrimePrefix s
                           of Just (first, _) -> if predicate first then Result rest first else Failure "satisfy"
                              Nothing -> p

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s Char
satisfyChar predicate = p
   where p = Delay (Failure "satisfyChar") f
         f [] = p
         f i@((_, s):tl) = case splitPrimePrefix s
                           of Just (first, rest) ->
                                 case Textual.characterPrefix first
                                 of Just c -> if predicate c then Result tl c else Failure "satisfyChar"
                                    Nothing -> if null rest then p else Failure "satisfyChar"
                              Nothing -> p

-- | A parser that consumes and returns the given prefix of the input.
string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s, Functor1 g) => s -> Parser g s s
string x | null x = pure x
string x = Delay (Failure $ "string " ++ show x) $
           \case i@((_, y):_)-> case (stripPrefix x y, stripPrefix y x)
                                of (Just y', _) -> Result (drop (length x) i) x
                                   (Nothing, Nothing) -> Failure "string"
                                   (Nothing, Just x') -> string x' *> pure x
                 [] -> string x

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
skipCharsWhile :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s ()
skipCharsWhile pred = while
   where while = Delay (pure ()) f
         f i@((_, s):_) = let (prefix, suffix) = Textual.span_ False pred s
                          in if null suffix then while
                             else Result (drop (length prefix) i) ()

inputWith [] = mempty
inputWith ((_, s):_) = s
