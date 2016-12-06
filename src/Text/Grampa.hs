{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Classes
   MonoidNull, FactorialMonoid, TextualMonoid,
   -- * Types
   Grammar, GrammarBuilder, Parser, ParseResults,
   -- * Grammar and parser manipulation
   fixGrammar, fixGrammarInput, parse, parseAll, simpleParse,
   -- * Parser combinators
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead,
   -- * Parsing primitives
   module Text.Parser.Char,
   module Text.Parser.Token,
   endOfInput, getInput, anyToken, token, satisfy, satisfyChar, spaces, string,
   scan, scanChars, takeWhile, takeWhile1, takeCharsWhile, takeCharsWhile1, skipCharsWhile)
where

import Control.Applicative
import Data.Char (isSpace)
import Data.List (genericLength, nub)
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

import Debug.Trace (trace)

import Prelude hiding (length, null, span, takeWhile)

type GrammarBuilder g g' s = g (Parser g' s) -> g (Parser g' s)
type ParseResults r = Either (Int, [String]) [r]

parse :: (FactorialMonoid s, Rank2.Apply g, Rank2.Traversable g, Rank2.Reassemblable g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults (r, s)
parse g prod input = fromResultList input (prod $ fst $ head $ fixGrammarInput (selfReferring g) g input)

parseAll :: (FactorialMonoid s, Rank2.Apply g, Rank2.Traversable g, Rank2.Reassemblable g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults r
parseAll g prod input = (fst <$>) <$> fromResultList input (prod $ fst $ head $ fixGrammarInput close g input)
   where close = Rank2.fmap (<* endOfInput) $ selfReferring g

simpleParse :: FactorialMonoid s => Parser (Rank2.Singleton r) s r -> s -> ParseResults (r, s)
simpleParse p = parse (Rank2.Singleton p) Rank2.getSingle

fromResultList :: FactorialMonoid s => s -> ResultList g s r -> ParseResults (r, s)
fromResultList s (ResultList (Left (FailureInfo _ pos msgs))) = Left (length s - fromIntegral pos, nub msgs)
fromResultList _ (ResultList (Right rl)) = Right (f <$> rl)
   where f (ResultInfo ((_, s):_) r) = (r, s)

instance MonoidNull s => Parsing (Parser g s) where
   try p = Parser{continued= \t rc fc-> continued p t rc (fc . weaken),
                  direct= \s t-> weakenResults (direct p s t),
                  recursive= \g s t-> weakenResults (recursive p g s t)}
      where weaken (FailureInfo s pos msgs) = FailureInfo (pred s) pos msgs
            weakenResults (InitialResultList (Left err)) = InitialResultList (Left $ weaken err)
            weakenResults rl = rl
   p <?> msg  = Parser{continued= \t rc fc-> continued p t rc (fc . strengthen),
                       direct= \s t-> strengthenResults (direct p s t),
                       recursive= \g s t-> strengthenResults (recursive p g s t)}
      where strengthen (FailureInfo s pos _msgs) = FailureInfo (succ s) pos [msg]
            strengthenResults (InitialResultList (Left err)) = InitialResultList (Left $ strengthen err)
            strengthenResults rl = rl
   notFollowedBy p = Parser{continued= \t rc fc-> either
                              (const $ rc () t)
                              (\rs-> if null rs then rc () t
                                     else fc (FailureInfo 1 (genericLength t) ["notFollowedBy"]))
                              (resultList $ continued p t succeed concede),
                            direct= \s t-> either
                              (const $ InitialResultList $ Right [StuckResultInfo ()])
                              (\rs -> InitialResultList $
                                      if null rs then Right [StuckResultInfo ()]
                                      else Left (FailureInfo 0 (genericLength t) ["notFollowedBy"]))
                              (initialResultList $ direct p s t),
                            recursive= \g s t-> either
                              (const $ InitialResultList $ Right [StuckResultInfo ()])
                              (\rs -> InitialResultList $
                                      if null rs then Right []
                                      else Left (FailureInfo 0 (genericLength t) ["notFollowedBy"]))
                              (initialResultList $ recursive p g s t)}
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = primitive (\_s _t _ _ fc -> fc msg)
   eof = endOfInput

instance MonoidNull s => LookAheadParsing (Parser g s) where
   lookAhead p = Parser{continued= \t rc fc-> continued p t (\r _-> rc r t) fc,
                        direct= \s t-> restoreResultInputs (direct p s t),
                        recursive= \g s t-> restoreResultInputs (recursive p g s t)}
               where restoreResultInputs rl@(InitialResultList Left{}) = rl
                     restoreResultInputs (InitialResultList (Right rl)) = InitialResultList (Right $ rewind <$> rl)
                     rewind (CompleteResultInfo _ r) = StuckResultInfo r
                     rewind (StuckResultInfo r) = StuckResultInfo r

instance (Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Show s, TextualMonoid s) => TokenParsing (Parser g s)

spaces :: (TextualMonoid t) => Parser g t ()
spaces = skipCharsWhile isSpace

-- | A parser that fails on any input and succeeds at its end
endOfInput :: (MonoidNull s) => Parser g s ()
endOfInput = primitive f
   where f s _t rc0 _rc fc
            | null s = rc0 ()
            | otherwise = fc "endOfInput"

-- | Always sucessful parser that returns the remaining input without consuming it.
getInput :: (MonoidNull s) => Parser g s s
getInput = primitive f
   where f s t rc0 rc _fc
            | null s = rc0 s
            | otherwise = rc s [last t]

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeWhile :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
takeWhile predicate = primitive f
   where f s t rc0 rc _fc = if null prefix then rc0 prefix else rc prefix (drop (length prefix - 1) t)
            where prefix = Factorial.takeWhile predicate s

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
takeWhile1 predicate = primitive f
   where f s t _rc0 rc fc
            | null prefix = fc "takeCharsWhile1"
            | otherwise = rc prefix (drop (length prefix - 1) t)
            where prefix = Factorial.takeWhile predicate s

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeCharsWhile :: (TextualMonoid s) => (Char -> Bool) -> Parser g s s
takeCharsWhile predicate = primitive f
   where f s t rc0 rc _fc = if null prefix then rc0 prefix else rc prefix (drop (length prefix - 1) t)
            where prefix = Textual.takeWhile_ False predicate s

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s) => (Char -> Bool) -> Parser g s s
takeCharsWhile1 predicate = primitive f
   where f s t _rc0 rc fc
            | null prefix = fc "takeCharsWhile1"
            | otherwise = rc prefix (drop (length prefix - 1) t)
            where prefix = Textual.takeWhile_ False predicate s

-- | A stateful scanner.  The predicate consumes and transforms a state argument, and each transformed state is passed
-- to successive invocations of the predicate on each token of the input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first prime
-- input factor.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scan :: (FactorialMonoid t) => s -> (s -> t -> Maybe s) -> Parser g t t
scan s0 f = primitive (go s0)
 where go s i t rc0 rc _fc = if null prefix then rc0 prefix else rc prefix (drop (length prefix - 1) t)
          where (prefix, _, _) = spanMaybe' s f i

-- | A stateful scanner.  The predicate consumes and transforms a
-- state argument, and each transformed state is passed to successive invocations of the predicate on each token of the
-- input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first character.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scanChars :: (TextualMonoid t) => s -> (s -> Char -> Maybe s) -> Parser g t t
scanChars s0 f = primitive (go s0)
 where go s i t rc0 rc _fc = if null prefix then rc0 prefix else rc prefix (drop (length prefix - 1) t)
          where (prefix, _, _) = Textual.spanMaybe_' s f i

-- | A parser that accepts any single input atom.
anyToken :: (FactorialMonoid s) => Parser g s s
anyToken = primitive f
   where f s t _rc0 rc fc =
            case splitPrimePrefix s
            of Just (first, _) -> rc first t
               _ -> fc "anyToken"

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s) => s -> Parser g s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
satisfy predicate = primitive f
   where f s t _rc0 rc fc =
            case splitPrimePrefix s
            of Just (first, _) | predicate first -> rc first t
               _ -> fc "satisfy"

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: (TextualMonoid s) => (Char -> Bool) -> Parser g s Char
satisfyChar predicate = primitive f
   where f s t _rc0 rc fc =
            case Textual.splitCharacterPrefix s
            of Just (first, _) | predicate first -> rc first t
               _ -> fc "satisfyChar"

-- | A parser that consumes and returns the given prefix of the input.
string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s) => s -> Parser g s s
string x | null x = pure x
string x = primitive $ \y t _rc0 rc fc-> 
   case stripPrefix x y
   of Just{} -> rc x (drop (length x - 1) t)
      _ -> fc ("string " ++ show x)

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
skipCharsWhile :: (TextualMonoid s) => (Char -> Bool) -> Parser g s ()
skipCharsWhile predicate = primitive f
   where f s t rc0 rc _fc = if null prefix then rc0 () else rc () (drop (length prefix - 1) t)
            where prefix = Textual.takeWhile_ False predicate s
