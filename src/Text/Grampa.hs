{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
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
import Data.Char (isSpace)
import Data.Monoid.Cancellative (LeftReductiveMonoid (stripPrefix))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(length, spanMaybe', splitPrimePrefix))
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.String (fromString)
import qualified Text.Parser.Char as CharParsing
import Text.Parser.Char (CharParsing(char, notChar, anyChar, text))
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))
import Text.Parser.Token (TokenParsing)

import qualified Rank2
import Text.Grampa.Types

import Prelude hiding (length, null, span, takeWhile)

type GrammarBuilder g g' s = g (Parser g' s) -> g (Parser g' s)
type ParseResults r = Either FailureInfo [r]

parse :: (FactorialMonoid s, Rank2.Alternative g, Rank2.Traversable g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults (r, s)
parse g prod input = fromResultList input (prod $ fst $ head $ fixGrammarInput g input)

parseAll :: (FactorialMonoid s, Rank2.Alternative g, Rank2.Traversable g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults r
parseAll g prod input =
   ((fst <$>) . filter (null . snd)) <$> fromResultList input (prod $ fst $ head $ fixGrammarInput g input)

simpleParse :: (FactorialMonoid s) => Parser (Rank2.Singleton r) s r -> s -> ParseResults (r, s)
simpleParse p = parse (Rank2.Singleton p) Rank2.getSingle

fromResultList :: s -> ResultList g s r -> Either FailureInfo [(r, s)]
fromResultList _ (ResultList (Left err)) = Left err
fromResultList _ (ResultList (Right rl)) = Right (f <$> rl)
   where f (ResultInfo _ s' _ r) = (r, s')

failureStrength :: Maybe x -> Int
failureStrength = maybe 0 (const 1)

instance (Rank2.Functor g, MonoidNull s) => Parsing (Parser g s) where
   try (P p) = P f
      where f g s t rc fc = p g s t rc (fc . weaken)
            weaken (FailureInfo s pos msgs) = FailureInfo (pred s) pos msgs
   P p <?> msg  = P f
      where f g s t rc fc = p g s t rc (fc . strengthen)
            strengthen (FailureInfo s pos _msgs) = FailureInfo (succ s) pos [msg]
   notFollowedBy (P p) = P f
      where f g s t rc fc = either
               (const $ rc $ ResultInfo g s t ())
               (\rs -> if null rs then rc (ResultInfo g s t ())
                       else fc (FailureInfo (failureStrength g) (fromIntegral $ length t) ["notFollowedBy"]))
               (resultList $ gd2rl (error "notFollowedBy nonTerminal") $ p g s t (pure . pure) concede)
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = P (\g _ t _ fc -> fc (FailureInfo (failureStrength g) (fromIntegral $ length t) [msg]))
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

spaces :: (TextualMonoid t) => Parser g t ()
spaces = skipCharsWhile isSpace

-- | A parser that fails on any input and succeeds at its end
endOfInput :: (MonoidNull s) => Parser g s ()
endOfInput = P f
   where f g s t rc fc
            | null s = rc (ResultInfo g s t ())
            | otherwise = fc (FailureInfo (failureStrength g) (fromIntegral $ length t) ["endOfInput"])

-- | Always sucessful parser that returns the remaining input without consuming it.
getInput :: (MonoidNull s) => Parser g s s
getInput = P f
   where f g s t rc _fc = rc (if null s then ResultInfo g s t s
                              else let (g', s') = last t in ResultInfo (Just g') s' [] s)

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeWhile :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
takeWhile predicate = P f
   where f g s t rc _fc = rc (if null prefix then ResultInfo g s t prefix else ResultInfo (Just g') s' t' prefix)
            where prefix = Factorial.takeWhile predicate s
                  (g', s'):t' = drop (length prefix - 1) t

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
takeWhile1 predicate = P f
   where f g s t rc fc
            | null prefix = fc (FailureInfo (failureStrength g) (fromIntegral $ length t) ["takeCharsWhile1"])
            | otherwise = rc (ResultInfo (Just g') s' t' prefix)
            where prefix = Factorial.takeWhile predicate s
                  (g', s'):t' = drop (length prefix - 1) t

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeCharsWhile :: (TextualMonoid s) => (Char -> Bool) -> Parser g s s
takeCharsWhile predicate = P f
   where f g s t rc _fc = rc (if null prefix then ResultInfo g s t prefix else ResultInfo (Just g') s' t' prefix)
            where prefix = Textual.takeWhile_ False predicate s
                  (g', s'):t' = drop (length prefix - 1) t

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s) => (Char -> Bool) -> Parser g s s
takeCharsWhile1 predicate = P f
   where f g s t rc fc
            | null prefix = fc (FailureInfo (failureStrength g) (fromIntegral $ length t) ["takeCharsWhile1"])
            | otherwise = rc (ResultInfo (Just g') s' t' prefix)
            where prefix = Textual.takeWhile_ False predicate s
                  (g', s'):t' = drop (length prefix - 1) t

-- | A stateful scanner.  The predicate consumes and transforms a state argument, and each transformed state is passed
-- to successive invocations of the predicate on each token of the input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first prime
-- input factor.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scan :: (FactorialMonoid t) => s -> (s -> t -> Maybe s) -> Parser g t t
scan s0 f = P (go s0)
 where go s g i t rc _fc = rc (if null prefix then ResultInfo g i t prefix else ResultInfo (Just g') i' t' prefix)
          where (prefix, _, _) = spanMaybe' s f i
                (g', i'):t' = drop (length prefix - 1) t

-- | A stateful scanner.  The predicate consumes and transforms a
-- state argument, and each transformed state is passed to successive invocations of the predicate on each token of the
-- input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first character.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scanChars :: (TextualMonoid t) => s -> (s -> Char -> Maybe s) -> Parser g t t
scanChars s0 f = P (go s0)
 where go s g i t rc _fc = rc (if null prefix then ResultInfo g i t prefix else ResultInfo (Just g') i' t' prefix)
          where (prefix, _, _) = Textual.spanMaybe_' s f i
                (g', i'):t' = drop (length prefix - 1) t

-- | A parser that accepts any single input atom.
anyToken :: (FactorialMonoid s) => Parser g s s
anyToken = P f
   where f g s t rc fc =
            case splitPrimePrefix s
            of Just (first, _) | (g', s'):t' <- t -> rc (ResultInfo (Just g') s' t' first)
               _ -> fc (FailureInfo (failureStrength g) (fromIntegral $ length s) ["anyToken"])

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s) => s -> Parser g s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
satisfy predicate = P f
   where f g s t rc fc =
            case splitPrimePrefix s
            of Just (first, _) | predicate first, (g', s'):t' <- t -> rc (ResultInfo (Just g') s' t' first)
               _ -> fc (FailureInfo (failureStrength g) (fromIntegral $ length s) ["satisfy"])

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: (TextualMonoid s) => (Char -> Bool) -> Parser g s Char
satisfyChar predicate = P f
   where f g s t rc fc =
            case Textual.splitCharacterPrefix s
            of Just (first, _) | predicate first, (g', s'):t' <- t -> rc (ResultInfo (Just g') s' t' first)
               _ -> fc (FailureInfo (failureStrength g) (fromIntegral $ length s) ["satisfyChar"])

-- | A parser that consumes and returns the given prefix of the input.
string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s) => s -> Parser g s s
string x | null x = pure x
string x = P $ \g y t rc fc-> 
   case stripPrefix x y
   of Just{} | (g', s'):t' <- drop (length x - 1) t -> rc (ResultInfo (Just g') s' t' x)
      _ -> fc (FailureInfo (1 + failureStrength g) (fromIntegral $ length t) ["string " ++ show x])

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
skipCharsWhile :: (TextualMonoid s) => (Char -> Bool) -> Parser g s ()
skipCharsWhile predicate = P f
   where f g s t rc _fc = rc (if null prefix then ResultInfo g s t () else ResultInfo (Just g') s' t' ())
            where prefix = Textual.takeWhile_ False predicate s
                  (g', s'):t' = drop (length prefix - 1) t
