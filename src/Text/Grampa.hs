{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa (
   -- * Rank 2
   module Rank2,
   -- * Classes
   MonoidNull, FactorialMonoid, TextualMonoid,
   -- * Types
   FailureInfo(..), Grammar, GrammarBuilder, Parser, ParseResults,
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

import qualified Rank2
import Text.Grampa.Types

import Debug.Trace (trace)

import Prelude hiding (length, null, span, takeWhile)

type GrammarBuilder g g' s = g (Parser g' s) -> g (Parser g' s)
type ParseResults r = Either FailureInfo [r]

parse :: (FactorialMonoid s, Rank2.Alternative g, Rank2.Reassemblable g, Rank2.Traversable g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults (r, s)
parse g prod input = fromResultList input (prod $ fst $ head $ fixGrammarInput g input)

parseAll :: (FactorialMonoid s, Rank2.Alternative g, Rank2.Reassemblable g, Rank2.Traversable g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults r
parseAll g prod input =
   ((fst <$>) . filter (null . snd)) <$> fromResultList input (prod $ fst $ head $ fixGrammarInput g input)

simpleParse :: (FactorialMonoid s) => Parser (Rank2.Singleton r) s r -> s -> ParseResults (r, s)
simpleParse p = parse (Rank2.Singleton p) Rank2.getSingle

fromResultList :: Monoid s => s -> ResultList g s r -> Either FailureInfo [(r, s)]
fromResultList _ (ResultList (Left err)) = Left err
fromResultList s (ResultList (Right rl)) = Right (f <$> rl)
   where f (ResultInfo g s' t r) = (r, s')

failureStrength :: Maybe x -> Int
failureStrength = maybe 0 (const 1)

instance (Rank2.Functor g, MonoidNull s) => Parsing (Parser g s) where
   try (P p) = P f
      where f g s t cont = strengthenBy pred <$> p g s t ((strengthenBy succ <$>) . cont)
            strengthenBy :: (Int -> Int) -> ResultList g s r -> ResultList g s r
            strengthenBy f (ResultList (Left (FailureInfo s pos msgs))) = ResultList (Left $ FailureInfo (f s) pos msgs)
            strengthenBy _ rl = rl
   P p <?> msg  = P f
      where f g s t cont = applyMsg <$> p g s t ((wrap <$>) . cont)
               where wrap :: ResultList g s r -> ResultList g s (Either FailureInfo [ResultInfo g s r])
                     wrap (ResultList (Left err)) = ResultList (Right [ResultInfo g s t $ Left err])
                     wrap (ResultList (Right rs)) = ResultList (Right [ResultInfo g s t $ Right rs])
            applyMsg :: ResultList g s (Either FailureInfo [ResultInfo g s r]) -> ResultList g s r
            applyMsg (ResultList (Left (FailureInfo s pos _))) = ResultList (Left $ FailureInfo (succ s) pos [msg])
            applyMsg (ResultList (Right [ResultInfo g s t (Left err)])) = ResultList (Left err)
            applyMsg (ResultList (Right [ResultInfo g s t (Right rs)])) = ResultList (Right rs)
   notFollowedBy (P p) = P f
      where f g s t cont = either
               (const $ cont $ ResultInfo g s t ())
               (\rs -> if null rs then cont (ResultInfo g s t ())
                       else concede (FailureInfo (failureStrength g) (fromIntegral $ length t) ["notFollowedBy"]))
               (resultList $ gd2rl (error "notFollowedBy nonTerminal") $ p g s t (pure . pure))
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = P (\g _ t _-> concede (FailureInfo (failureStrength g) (fromIntegral $ length t) [msg]))
   eof = endOfInput

instance (Rank2.Functor g, MonoidNull s) => LookAheadParsing (Parser g s) where
   lookAhead (P p) = P f
      where f g s t cont = p g s t (cont . restoreInput)
               where restoreInput (ResultInfo _ _ _ r) = ResultInfo g s t r

instance (Rank2.Functor g, Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Rank2.Functor g, Show s, TextualMonoid s) => TokenParsing (Parser g s)

spaces :: (Rank2.Functor g, Show t, TextualMonoid t) => Parser g t ()
spaces = skipCharsWhile isSpace

-- | A parser that fails on any input and succeeds at its end
endOfInput :: (MonoidNull s, Rank2.Functor g) => Parser g s ()
endOfInput = P f
   where f g s t cont
            | null s = cont (ResultInfo g s t ())
            | otherwise = concede (FailureInfo (failureStrength g) (fromIntegral $ length t) ["endOfInput"])

-- | Always sucessful parser that returns the remaining input without consuming it.
getInput :: (MonoidNull s, Rank2.Functor g) => Parser g s s
getInput = P f
   where f g s t cont = cont (if null s then ResultInfo g s t s
                              else let (g', s') = last t in ResultInfo (Just g') s' [] s)

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeWhile :: (FactorialMonoid s, Rank2.Functor g) => (s -> Bool) -> Parser g s s
takeWhile pred = P f
   where f g s t cont = cont (if null prefix then ResultInfo g s t prefix else ResultInfo (Just g') s' t' prefix)
            where prefix = Factorial.takeWhile pred s
                  (g', s'):t' = drop (length prefix - 1) t

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s, Rank2.Functor g) => (s -> Bool) -> Parser g s s
takeWhile1 pred = P f
   where f g s t cont
            | null prefix = concede (FailureInfo (failureStrength g) (fromIntegral $ length t) ["takeCharsWhile1"])
            | otherwise = cont (ResultInfo (Just g') s' t' prefix)
            where prefix = Factorial.takeWhile pred s
                  (g', s'):t' = drop (length prefix - 1) t

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeCharsWhile :: (TextualMonoid s, Rank2.Functor g) => (Char -> Bool) -> Parser g s s
takeCharsWhile pred = P f
   where f g s t cont = cont (if null prefix then ResultInfo g s t prefix else ResultInfo (Just g') s' t' prefix)
            where (prefix, suffix) = Textual.span_ False pred s
                  (g', s'):t' = drop (length prefix - 1) t

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s, Rank2.Functor g) => (Char -> Bool) -> Parser g s s
takeCharsWhile1 pred = P f
   where f g s t cont
            | null prefix = concede (FailureInfo (failureStrength g) (fromIntegral $ length t) ["takeCharsWhile1"])
            | otherwise = cont (ResultInfo (Just g') s' t' prefix)
            where (prefix, suffix) = Textual.span_ False pred s
                  (g', s'):t' = drop (length prefix - 1) t

-- | A stateful scanner.  The predicate consumes and transforms a state argument, and each transformed state is passed
-- to successive invocations of the predicate on each token of the input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first prime
-- input factor.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scan :: (FactorialMonoid t, Show t, Rank2.Functor g) => s -> (s -> t -> Maybe s) -> Parser g t t
scan s0 f = P (go s0)
 where go s g i t cont = cont (if null prefix then ResultInfo g i t prefix else ResultInfo (Just g') i' t' prefix)
          where (prefix, suffix, _) = spanMaybe' s f i
                (g', i'):t' = drop (length prefix - 1) t

-- | A stateful scanner.  The predicate consumes and transforms a
-- state argument, and each transformed state is passed to successive invocations of the predicate on each token of the
-- input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first character.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scanChars :: (TextualMonoid t, Show t, Rank2.Functor g) => s -> (s -> Char -> Maybe s) -> Parser g t t
scanChars s0 f = P (go s0)
 where go s g i t cont = cont (if null prefix then ResultInfo g i t prefix else ResultInfo (Just g') i' t' prefix)
          where (prefix, suffix, _) = Textual.spanMaybe_' s f i
                (g', i'):t' = drop (length prefix - 1) t

-- | A parser that accepts any single input atom.
anyToken :: (FactorialMonoid s, Rank2.Functor g) => Parser g s s
anyToken = P f
   where f g s t cont =
            case splitPrimePrefix s
            of Just (first, _) | (g', s'):t' <- t -> cont (ResultInfo (Just g') s' t' first)
               Nothing -> concede (FailureInfo (failureStrength g) (fromIntegral $ length s) ["anyToken"])

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s, Rank2.Functor g) => s -> Parser g s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: (FactorialMonoid s, Rank2.Functor g) => (s -> Bool) -> Parser g s s
satisfy predicate = P f
   where f g s t cont =
            case splitPrimePrefix s
            of Just (first, _) | predicate first, (g', s'):t' <- t -> cont (ResultInfo (Just g') s' t' first)
               _ -> concede (FailureInfo (failureStrength g) (fromIntegral $ length s) ["satisfy"])

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: (TextualMonoid s, Rank2.Functor g) => (Char -> Bool) -> Parser g s Char
satisfyChar predicate = P f
   where f g s t cont =
            case Textual.splitCharacterPrefix s
            of Just (first, _) | predicate first, (g', s'):t' <- t -> cont (ResultInfo (Just g') s' t' first)
               _ -> concede (FailureInfo (failureStrength g) (fromIntegral $ length s) ["satisfyChar"])

-- | A parser that consumes and returns the given prefix of the input.
string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s, Rank2.Functor g) => s -> Parser g s s
string x | null x = pure x
string x = P $ \g y t cont-> 
   case stripPrefix x y
   of Just y' | (g', s'):t' <- drop (length x - 1) t -> cont (ResultInfo (Just g') s' t' x)
      _ -> concede (FailureInfo (1 + failureStrength g) (fromIntegral $ length t) ["string " ++ show x])

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
skipCharsWhile :: (TextualMonoid s, Rank2.Functor g) => (Char -> Bool) -> Parser g s ()
skipCharsWhile pred = P f
   where f g s t cont = cont (if null prefix then ResultInfo g s t () else ResultInfo (Just g') s' t' ())
            where (prefix, suffix) = Textual.span_ False pred s
                  (g', s'):t' = drop (length prefix - 1) t
