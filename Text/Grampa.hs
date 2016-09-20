{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa (
   -- * Classes
   Functor1(..), Apply1(..), Alternative1(..), Foldable1(..), Traversable1(..), Reassemblable(..),
   MonoidNull, FactorialMonoid, TextualMonoid,
   -- * Types
   Grammar, GrammarBuilder, Parser, Empty1(..), Singleton1(..), Identity1(..), Product1(..), Arrow1(..),
   -- * Grammar and parser manipulation
   feed, feedEnd, fixGrammar, fixGrammarInput, parse, parseAll,
   -- * Parser combinators
   iterateMany, lookAhead, notFollowedBy,
   -- * Parsing primitives
   endOfInput, getInput, anyToken, token, satisfy, satisfyChar, string,
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

import Text.Grampa.Types

import Prelude hiding (length, null, span, takeWhile)

parse :: (FactorialMonoid s, Alternative1 g, Reassemblable g, Traversable1 g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> [(r, s)]
parse g prod input = resultsAndRest (prod $ fst $ head $ fixGrammarInput g input)

parseAll :: (FactorialMonoid s, Alternative1 g, Reassemblable g, Traversable1 g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> [r]
parseAll g prod input = fst <$> filter (null . snd) (resultsAndRest $ prod $ fst $ head $ fixGrammarInput g input)

resultsAndRest :: Monoid s => ResultList g s r -> [(r, s)]
resultsAndRest (ResultList rl) = f <$> rl
   where f (_, [], r) = (r, mempty)
         f (_, (_, s):_, r) = (r, s)

-- | Behaves like the argument parser, but without consuming any input.
lookAhead :: (MonoidNull s, Functor1 g) => Parser g s r -> Parser g s r
lookAhead = lookAheadInto Stuck []
   where -- lookAheadInto :: [(g (Parser g s), s)] -> Parser g s r -> Parser g s r
         lookAheadInto _ _ p@Failure{}        = p
         lookAheadInto is t (Result _ _ r)     = Result is t r
         lookAheadInto is t (Choice p1 p2)     = lookAheadInto is t p1 <|> lookAheadInto is t p2
         lookAheadInto is t (Delay e f)        = Delay (lookAheadInto is t e) (\is s-> lookAheadInto is (mappend t s) (f is s))

-- | Does not consume any input; succeeds (with 'mempty' result) iff the argument parser fails.
notFollowedBy :: (MonoidNull s, Functor1 g) => Parser g s r -> Parser g s ()
notFollowedBy = lookAheadNotInto Stuck []
   where -- lookAheadNotInto :: (Monoid s, Monoid r) => [(g (Parser g s), s)] -> Parser g s r -> Parser g s ()
         lookAheadNotInto is t Failure{}   = Result is t mempty
         lookAheadNotInto _ t Result{}   = Failure "notFollowedBy"
         lookAheadNotInto is t (Delay e f) = Delay (lookAheadNotInto is t e) (\is s-> lookAheadNotInto is (mappend t s) (f is s))
         lookAheadNotInto is t p = Delay (lookAheadNotInto is t $ feedEnd p) (\is s-> lookAheadNotInto is (mappend t s) (feed s p))

-- | A parser that fails on any input and succeeds at its end
endOfInput :: (MonoidNull s, Functor1 g) => Parser g s ()
endOfInput = Delay (pure ()) (const f)
   where f [] = endOfInput
         f ((_, s):_) | null s = endOfInput
         f _ = Failure "endOfInput"

-- | Always sucessful parser that returns the remaining input without consuming it.
getInput :: (MonoidNull s, Functor1 g) => Parser g s s
getInput = Delay (pure mempty) f
   where f _ [] = getInput
         f is i@((_, s):_) = Result is i s

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeWhile :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
takeWhile pred = while
   where while = Delay (pure mempty) f
         f _ [] = while
         f is i@((_, s):_) = let (prefix, suffix) = span pred s
                             in if null suffix then resultPart (mappend prefix) while
                                else Result (if null prefix then is else Advanced) (drop (length prefix) i) prefix

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
takeWhile1 pred = Delay (Failure "takeWhile1") (const f)
   where f [] = takeWhile1 pred
         f i@((_, s):_) | null s = takeWhile1 pred
                        | otherwise = let (prefix, suffix) = span pred s
                                      in if null prefix then Failure "takeWhile1"
                                         else if null suffix then resultPart (mappend prefix) (takeWhile pred)
                                              else Result Advanced (drop (length prefix) i) prefix

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeCharsWhile :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s s
takeCharsWhile pred = while
   where while = Delay (pure mempty) f
         f _ [] = while
         f is i@((_, s):_) = let (prefix, suffix) = Textual.span_ False pred s
                             in if null suffix then resultPart (mappend prefix) while
                                else Result (if null prefix then is else Advanced) (drop (length prefix) i) prefix

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s s
takeCharsWhile1 pred = Delay (Failure "takeCharsWhile1") (const f)
   where f [] = takeCharsWhile1 pred
         f i@((_, s):_) | null s = takeCharsWhile1 pred
                        | otherwise = let (prefix, suffix) = Textual.span_ False pred s
                                      in if null prefix
                                         then Failure "takeCharsWhile1"
                                         else if null suffix then resultPart (mappend prefix) (takeCharsWhile pred)
                                              else Result Advanced (drop (length prefix) i) prefix

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
 where go s is i@((_, t):_) = let (prefix, suffix, s') = spanMaybe' s f t
                              in if null suffix then resultPart (mappend prefix) (scan s' f)
                                 else Result (if null prefix then is else Advanced) (drop (length prefix) i) prefix

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
 where go s is i@((_, t):_) = let (prefix, suffix, s') = Textual.spanMaybe_' s f t
                              in if null suffix then resultPart (mappend prefix) (scanChars s' f)
                                 else Result (if null prefix then is else Advanced) (drop (length prefix) i) prefix

-- | A parser that accepts any single input atom.
anyToken :: (FactorialMonoid s, Functor1 g) => Parser g s s
anyToken = Delay (Failure "anyToken") (const f)
   where f [] = anyToken
         f ((_, s):rest) = case splitPrimePrefix s
                           of Just (first, _) -> Result Advanced rest first
                              Nothing -> anyToken

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s, Functor1 g) => s -> Parser g s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
satisfy predicate = p
   where p = Delay (Failure "satisfy") (const f)
         f [] = p
         f ((_, s):rest) = case splitPrimePrefix s
                           of Just (first, _)
                                 | predicate first -> Result Advanced rest first
                                 | otherwise -> Failure "satisfy"
                              Nothing -> p

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s Char
satisfyChar predicate = p
   where p = Delay (Failure "satisfyChar") (const f)
         f [] = p
         f i@((_, s):tl) = case splitPrimePrefix s
                           of Just (first, rest) ->
                                 case Textual.characterPrefix first
                                 of Just c | predicate c -> Result Advanced tl c
                                    _ -> Failure "satisfyChar"
                              Nothing -> p

-- | A parser that consumes and returns the given prefix of the input.
string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s, Functor1 g) => s -> Parser g s s
string x | null x = pure x
string x = Delay (Failure $ "string " ++ show x) $ const $
           \case i@((_, y):_)-> case (stripPrefix x y, stripPrefix y x)
                                of (Just y', _) -> Result Advanced (drop (length x) i) x
                                   (Nothing, Nothing) -> Failure "string"
                                   (Nothing, Just x') -> string x' *> pure x
                 [] -> string x

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
skipCharsWhile :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s ()
skipCharsWhile pred = while
   where while = Delay (pure ()) f
         f _ [] = while
         f is i@((_, s):_) = let (prefix, suffix) = Textual.span_ False pred s
                             in if null suffix then while
                                else Result (if null prefix then is else Advanced) (drop (length prefix) i) ()

resultPart :: (r -> r) -> Parser g s r -> Parser g s r
resultPart f p = f <$> p
