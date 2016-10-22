{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa (
   -- * Classes
   Functor1(..), Apply1(..), Alternative1(..), Foldable1(..), Traversable1(..), Reassemblable(..),
   MonoidNull, FactorialMonoid, TextualMonoid,
   -- * Types
   FailureInfo(..), Grammar, GrammarBuilder, Parser, ParseResults,
   Empty1(..), Singleton1(..), Identity1(..), Product1(..), Arrow1(..),
   -- * Grammar and parser manipulation
   fixGrammar, fixGrammarInput, parse, parseAll, simpleParse,
   -- * Parser combinators
   lookAhead, notFollowedBy,
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
import qualified Data.Monoid.Factorial as Factorial
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

import Debug.Trace (trace)

import Prelude hiding (length, null, span, takeWhile)

type ParseResults r = Either FailureInfo [r]

parse :: (FactorialMonoid s, Alternative1 g, Reassemblable g, Traversable1 g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults (r, s)
parse g prod input = fromResultList input (prod $ fst $ head $ fixGrammarInput g input)

parseAll :: (FactorialMonoid s, Alternative1 g, Reassemblable g, Traversable1 g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults r
parseAll g prod input =
   ((fst <$>) . filter (null . snd)) <$> fromResultList input (prod $ fst $ head $ fixGrammarInput g input)

simpleParse :: (FactorialMonoid s) => Parser (Singleton1 r) s r -> s -> ParseResults (r, s)
simpleParse p = parse (Singleton1 p) getSingle

fromResultList :: Monoid s => s -> ResultList g s r -> Either FailureInfo [(r, s)]
fromResultList _ (ResultList (Left err)) = Left err
fromResultList s (ResultList (Right rl)) = Right (f <$> rl)
   where f (ResultInfo Stuck _ r) = (r, s)
         f (ResultInfo _ [] r) = (r, mempty)
         f (ResultInfo _ ((_, s):_)  r) = (r, s)

instance (Functor1 g, MonoidNull s) => Parsing (Parser g s) where
   try = id
   (<?>) = const
   notFollowedBy = lookAheadNotInto Stuck []
      where -- lookAheadNotInto :: (Monoid s, Monoid r) => [(g (Parser g s), s)] -> Parser g s r -> Parser g s ()
            lookAheadNotInto _ _ (P p) = P f
               where f g s t = (ResultList . invert . resultList) <$> p g s t
                        where invert Left{} =  Right [ResultInfo Stuck undefined ()]
                              invert (Right []) = Right []
                              invert Right{} = Left (FailureInfo (fromIntegral $ length t) ["notFollowedBy"])
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = P (\_ _ _-> concede (FailureInfo maxBound [msg]))
   eof = endOfInput

instance (Functor1 g, MonoidNull s) => LookAheadParsing (Parser g s) where
   lookAhead = lookAheadInto Stuck []
      where -- lookAheadInto :: [(g (Parser g s), s)] -> Parser g s r -> Parser g s r
            lookAheadInto _ _ (P p) = P f
               where f g s t = (ResultList . ((restoreInput <$>) <$>) . resultList) <$> p g s t
                        where restoreInput (ResultInfo _ _ r) = ResultInfo Stuck t r

instance (Functor1 g, Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Functor1 g, Show s, TextualMonoid s) => TokenParsing (Parser g s)

spaces :: (Functor1 g, Show t, TextualMonoid t) => Parser g t ()
spaces = skipCharsWhile isSpace

-- | A parser that fails on any input and succeeds at its end
endOfInput :: (MonoidNull s, Functor1 g) => Parser g s ()
endOfInput = P f
   where f g s t
            | null s = succeed (ResultInfo Stuck t ())
            | otherwise = concede (FailureInfo (fromIntegral $ length t) ["endOfInput"])

-- | Always sucessful parser that returns the remaining input without consuming it.
getInput :: (MonoidNull s, Functor1 g) => Parser g s s
getInput = P f
   where f g s t = succeed (ResultInfo (if null s then Stuck else Advanced) [last t] s)

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeWhile :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
takeWhile pred = P f
   where f g s t = succeed (ResultInfo (if null prefix then Stuck else Advanced) (drop (length prefix - 1) t) prefix)
            where prefix = Factorial.takeWhile pred s

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
takeWhile1 pred = P f
   where f g s t
            | null prefix = concede (FailureInfo (fromIntegral $ length t) ["takeCharsWhile1"])
            | otherwise = -- trace ("takeCharsWhile1 " ++ show (prefix, suffix)) $
                          succeed (ResultInfo Advanced (drop (length prefix - 1) t) prefix)
            where prefix = Factorial.takeWhile pred s

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeCharsWhile :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s s
takeCharsWhile pred = P f
   where f g s t = succeed (ResultInfo (if null prefix then Stuck else Advanced) (drop (length prefix - 1) t) prefix)
            where (prefix, suffix) = Textual.span_ False pred s

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s s
takeCharsWhile1 pred = P f
   where f g s t
            | null prefix = concede (FailureInfo (fromIntegral $ length t) ["takeCharsWhile1"])
            | otherwise = -- trace ("takeCharsWhile1 " ++ show (prefix, suffix)) $
                          succeed (ResultInfo Advanced (drop (length prefix - 1) t) prefix)
            where (prefix, suffix) = Textual.span_ False pred s

-- | A stateful scanner.  The predicate consumes and transforms a state argument, and each transformed state is passed
-- to successive invocations of the predicate on each token of the input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first prime
-- input factor.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scan :: (FactorialMonoid t, Show t, Functor1 g) => s -> (s -> t -> Maybe s) -> Parser g t t
scan s0 f = P (go s0)
 where go s g i t = succeed (ResultInfo (if null prefix then Stuck else Advanced) (drop (length prefix - 1) t) prefix)
          where (prefix, suffix, s') = spanMaybe' s f i

-- | A stateful scanner.  The predicate consumes and transforms a
-- state argument, and each transformed state is passed to successive invocations of the predicate on each token of the
-- input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first character.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scanChars :: (TextualMonoid t, Show t, Functor1 g) => s -> (s -> Char -> Maybe s) -> Parser g t t
scanChars s0 f = P (go s0)
 where go s g i t = succeed (ResultInfo (if null prefix then Stuck else Advanced) (drop (length prefix - 1) t) prefix)
          where (prefix, suffix, s') = Textual.spanMaybe_' s f i

-- | A parser that accepts any single input atom.
anyToken :: (FactorialMonoid s, Functor1 g) => Parser g s s
anyToken = P f
   where f g s t = case splitPrimePrefix s
                 of Just (first, _) -> succeed (ResultInfo Advanced t first)
                    Nothing -> concede (FailureInfo (fromIntegral $ length s) ["anyToken"])

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s, Functor1 g) => s -> Parser g s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: (FactorialMonoid s, Functor1 g) => (s -> Bool) -> Parser g s s
satisfy predicate = P f
   where f g s t = case splitPrimePrefix s
                 of Just (first, _) | predicate first -> succeed (ResultInfo Advanced t first)
                    _ -> concede (FailureInfo (fromIntegral $ length s) ["satisfy"])

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s Char
satisfyChar predicate = P f
   where f g s t = case Textual.splitCharacterPrefix s
                 of Just (first, _) | predicate first -> succeed (ResultInfo Advanced t first)
                    _ -> concede (FailureInfo (fromIntegral $ length s) ["satisfyChar"])

-- | A parser that consumes and returns the given prefix of the input.
string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s, Functor1 g) => s -> Parser g s s
string x | null x = pure x
string x = P $ \g y t-> 
   case stripPrefix x y
   of Just y' -> -- trace ("string " ++ show (x, y', snd $ head t)) $
                 succeed (ResultInfo Advanced (drop (length x - 1) t) x)
      _ -> concede (FailureInfo (fromIntegral $ length t) ["string " ++ show x])

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
skipCharsWhile :: (TextualMonoid s, Functor1 g) => (Char -> Bool) -> Parser g s ()
skipCharsWhile pred = while
   where while = P f
         f g s t = succeed (ResultInfo (if null prefix then Stuck else Advanced) (drop (length prefix - 1) t) ())
            where (prefix, suffix) = Textual.span_ False pred s
