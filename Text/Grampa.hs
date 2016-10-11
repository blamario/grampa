{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa (
   -- * Classes
   Functor1(..), Apply1(..), Alternative1(..), Foldable1(..), Traversable1(..), Reassemblable(..),
   MonoidNull, FactorialMonoid, TextualMonoid,
   -- * Types
   FailureInfo(..), Grammar, GrammarBuilder, Parser, ParseResults,
   Empty1(..), Singleton1(..), Identity1(..), Product1(..), Arrow1(..),
   -- * Grammar and parser manipulation
   feed, feedEnd, fixGrammar, fixGrammarInput, parse, parseAll, simpleParse,
   -- * Parser combinators
   iterateMany, lookAhead, notFollowedBy,
   -- * Parsing primitives
   endOfInput, getInput, anyToken, token, satisfy, satisfyChar, spaces, string,
   scan, scanChars, takeWhile, takeWhile1, takeCharsWhile, takeCharsWhile1, skipCharsWhile)
where

import Control.Applicative
import Control.Arrow (second)
import Data.Char (isSpace)
import Data.Function (fix)
import Data.Monoid (Monoid, mappend, mempty, (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid (stripPrefix))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(length, span, spanMaybe', splitPrimePrefix, tails))
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Textual as Textual
import Data.String (fromString)
import Data.Word (Word64)
import qualified Text.Parser.Char as CharParsing
import Text.Parser.Char (CharParsing(char, notChar, anyChar, text))
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))
import Text.Parser.Token (TokenParsing)

import Text.Grampa.Classes
import Text.Grampa.Types

import Prelude hiding (length, null, span, takeWhile)

type ParseResults r = Either FailureInfo [r]

parse :: (FactorialMonoid s, Alternative1 g, Reassemblable g, Traversable1 g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults (r, s)
parse g prod input = fromResultList (prod $ fst $ head $ fixGrammarInput g input)

parseAll :: (FactorialMonoid s, Alternative1 g, Reassemblable g, Traversable1 g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults r
parseAll g prod input =
   ((fst <$>) . filter (null . snd)) <$> fromResultList (prod $ fst $ head $ fixGrammarInput g input)

simpleParse :: FactorialMonoid s => Parser (Singleton1 r) s r -> s -> ParseResults (r, s)
simpleParse p = parse (Singleton1 p) getSingle

fromResultList :: Monoid s => ResultList g s r -> Either FailureInfo [(r, s)]
fromResultList (ResultList (Left err)) = Left err
fromResultList (ResultList (Right rl)) = Right (f <$> rl)
   where f (ResultInfo _ [] r) = (r, mempty)
         f (ResultInfo _ ((_, s):_)  r) = (r, s)

instance (Functor1 g, MonoidNull s) => Parsing (Parser g s) where
   try = id
   (<?>) = const
   notFollowedBy = lookAheadNotInto Stuck []
      where -- lookAheadNotInto :: (Monoid s, Monoid r) => [(g (Parser g s), s)] -> Parser g s r -> Parser g s ()
            lookAheadNotInto is t Failure{} = Result (ResultInfo is t mempty)
            lookAheadNotInto _ t Result{} = Failure (FailureInfo (fromIntegral $ length t) ["notFollowedBy"])
            lookAheadNotInto _ t (Choice Result{} _) = Failure (FailureInfo (fromIntegral $ length t) ["notFollowedBy"])
            lookAheadNotInto is t (Delay e f) =
               Delay (lookAheadNotInto is t e) (\is s-> lookAheadNotInto is (mappend t s) (f is s))
            lookAheadNotInto is t p =
               Delay (lookAheadNotInto is t $ feedEnd p) (\is s-> lookAheadNotInto is (mappend t s) (feed s p))
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = Failure (FailureInfo maxBound [msg])
   eof = endOfInput

instance (Functor1 g, MonoidNull s) => LookAheadParsing (Parser g s) where
   lookAhead = lookAheadInto Stuck []
      where -- lookAheadInto :: [(g (Parser g s), s)] -> Parser g s r -> Parser g s r
            lookAheadInto _ _ p@Failure{}     = p
            lookAheadInto is t (Result (ResultInfo _ _ r)) = Result (ResultInfo is t r)
            lookAheadInto is t (Choice p1 p2) = lookAheadInto is t p1 <|> lookAheadInto is t p2
            lookAheadInto is t (Delay e f)    = Delay (lookAheadInto is t e) (\is s-> lookAheadInto is (mappend t s) (f is s))

instance (Functor1 g, Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Functor1 g, Show s, TextualMonoid s) => TokenParsing (Parser g s)

spaces :: (Functor1 g, TextualMonoid t) => Parser g t ()
spaces = skipCharsWhile isSpace

-- | A parser that fails on any input and succeeds at its end
endOfInput :: (MonoidNull s, Functor1 g) => Parser g s ()
endOfInput = Delay (pure ()) (const f)
   where f [] = endOfInput
         f ((_, s):_) | null s = endOfInput
         f rest = Failure (FailureInfo (fromIntegral $ length rest) ["endOfInput"])

-- | Always sucessful parser that returns the remaining input without consuming it.
getInput :: (MonoidNull s, Functor1 g) => Parser g s s
getInput = Delay (pure mempty) f
   where f _ [] = getInput
         f is i@((_, s):_) = Result (ResultInfo is i s)

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeWhile :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
takeWhile pred = while
   where while = Delay (pure mempty) f
         f _ [] = while
         f is i@((_, s):_)
            | null suffix = resultPart (mappend prefix) while
            | otherwise = Result (ResultInfo (if null prefix then is else Advanced) (drop (length prefix) i) prefix)
            where (prefix, suffix) = span pred s

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
takeWhile1 pred = Delay (Failure $ FailureInfo 0 ["takeWhile1"]) (const f)
   where f [] = takeWhile1 pred
         f i@((_, s):_) | null s = takeWhile1 pred
                        | otherwise = let (prefix, suffix) = span pred s
                                      in if null prefix
                                         then Failure (FailureInfo (fromIntegral $ length i) ["takeWhile1"])
                                         else if null suffix then resultPart (mappend prefix) (takeWhile pred)
                                              else Result (ResultInfo Advanced (drop (length prefix) i) prefix)

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeCharsWhile :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s s
takeCharsWhile pred = while
   where while = Delay (pure mempty) f
         f _ [] = while
         f is i@((_, s):_)
            | null suffix = resultPart (mappend prefix) while
            | otherwise = Result (ResultInfo (if null prefix then is else Advanced) (drop (length prefix) i) prefix)
            where (prefix, suffix) = Textual.span_ False pred s

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s s
takeCharsWhile1 pred = Delay (Failure $ FailureInfo 0 ["takeCharsWhile1"]) (const f)
   where f [] = takeCharsWhile1 pred
         f i@((_, s):_)
            | null s = takeCharsWhile1 pred
            | null prefix = Failure (FailureInfo (fromIntegral $ length i) ["takeCharsWhile1"])
            | null suffix = resultPart (mappend prefix) (takeCharsWhile pred)
            | otherwise = Result (ResultInfo Advanced (drop (length prefix) i) prefix)
            where (prefix, suffix) = Textual.span_ False pred s

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
 where go s is i@((_, t):_)
          | null suffix = resultPart (mappend prefix) (scan s' f)
          | otherwise = Result (ResultInfo (if null prefix then is else Advanced) (drop (length prefix) i) prefix)
          where (prefix, suffix, s') = spanMaybe' s f t

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
 where go s is i@((_, t):_)
          | null suffix = resultPart (mappend prefix) (scanChars s' f)
          | otherwise = Result (ResultInfo (if null prefix then is else Advanced) (drop (length prefix) i) prefix)
          where (prefix, suffix, s') = Textual.spanMaybe_' s f t

-- | A parser that accepts any single input atom.
anyToken :: (FactorialMonoid s, Functor1 g) => Parser g s s
anyToken = Delay (Failure $ FailureInfo 0 ["anyToken"]) (const f)
   where f [] = anyToken
         f ((_, s):rest) = case splitPrimePrefix s
                           of Just (first, _) -> Result (ResultInfo Advanced rest first)
                              Nothing -> anyToken

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s, Functor1 g) => s -> Parser g s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
satisfy predicate = p
   where p = Delay (Failure $ FailureInfo 0 ["satisfy"]) (const f)
         f [] = p
         f i@((_, s):rest) = case splitPrimePrefix s
                             of Just (first, _)
                                   | predicate first -> Result (ResultInfo Advanced rest first)
                                   | otherwise -> Failure (FailureInfo (fromIntegral $ length i) ["satisfy"])
                                Nothing -> p

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s Char
satisfyChar predicate = p
   where p = Delay (Failure $ FailureInfo 0 ["satisfyChar"]) (const f)
         f [] = p
         f i@((_, s):tl) = case splitPrimePrefix s
                           of Just (first, rest) ->
                                 case Textual.characterPrefix first
                                 of Just c | predicate c -> Result (ResultInfo Advanced tl c)
                                    _ -> Failure (FailureInfo (fromIntegral $ length i) ["satisfyChar"])
                              Nothing -> p

-- | A parser that consumes and returns the given prefix of the input.
string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s, Functor1 g) => s -> Parser g s s
string x | null x = pure x
string x = Delay (Failure $ FailureInfo 0 ["string " ++ show x]) $ const $
           \case i@((_, y):_)-> case (stripPrefix x y, stripPrefix y x)
                                of (Just y', _) -> Result (ResultInfo Advanced (drop (length x) i) x)
                                   (Nothing, Nothing) ->
                                      Failure (FailureInfo (fromIntegral $ length i) ["string " ++ show x])
                                   (Nothing, Just x') -> string x' *> pure x
                 [] -> string x

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
skipCharsWhile :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s ()
skipCharsWhile pred = while
   where while = Delay (pure ()) f
         f _ [] = while
         f is i@((_, s):_)
            | null suffix = while
            | otherwise = Result (ResultInfo (if null prefix then is else Advanced) (drop (length prefix) i) ())
            where (prefix, suffix) = Textual.span_ False pred s

resultPart :: (r -> r) -> Parser g s r -> Parser g s r
resultPart f p = f <$> p
