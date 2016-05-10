{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa (
   -- * Classes
   Functor1(..), Foldable1(..), Traversable1(..), Reassemblable(..),
   MonoidNull, FactorialMonoid, TextualMonoid,
   -- * Types
   Grammar, GrammarBuilder, Parser, Production, Identity1(..), Product1(..),
   -- * Grammar and parser manipulation
   feed, feedEnd, feedGrammar, fixGrammar, parse, production, recursive, results,
   -- * Parser combinators
   iterateMany, lookAhead, notFollowedBy, endOfInput,
   -- * Parsing primitives
   anyToken, token, satisfy, satisfyChar, string,
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

recursive = Recursive

parse :: (Reassemblable g, FactorialMonoid s) => Grammar g s -> Production g s r -> [s] -> [r]
parse g prod chunks = fst <$> results ((<* endOfInput) $ prod
                                      $ fmap1 feedEnd
                                      $ foldr (feedGrammar g) g
                                      $ reverse chunks)

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
endOfInput = Delay (pure ()) f
   where f [] = endOfInput
         f ((_, s):_) | null s = endOfInput
         f _ = Failure "endOfInput"

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

resultPart :: (r -> r) -> Parser g s r -> Parser g s r
resultPart f p = f <$> p
