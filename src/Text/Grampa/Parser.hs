{-# LANGUAGE FlexibleContexts, InstanceSigs, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa.Parser (FailureInfo(..), ResultInfo(..), ResultList(..),
                           Grammar, Parser(..), ParseResults, fromResultList,
                           (<<|>), endOfInput, getInput, anyToken, token, satisfy, satisfyChar, string,
                           scan, scanChars, takeWhile, takeWhile1, takeCharsWhile, takeCharsWhile1, whiteSpace)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
import Data.Char (isSpace)
import Data.List (genericLength, nub)
import Data.Monoid (Monoid(mappend, mempty), (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid (isPrefixOf))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(length, splitPrimePrefix))
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.String (fromString)
import Data.Word (Word64)

import qualified Text.Parser.Char
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))
import Text.Parser.Token (TokenParsing(someSpace))

import Prelude hiding (iterate, length, null, span, takeWhile)

-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
newtype Parser g i r = Parser{applyParser :: [(i, g (ResultList g i))] -> ResultList g i r}
data ResultList g s r = Parsed [ResultInfo g s r]
                      | NoParse FailureInfo
data ResultInfo g s r = ResultInfo ![(s, g (ResultList g s))] !r
data FailureInfo = FailureInfo !Int Word64 [String] deriving (Eq, Show)
type ParseResults r = Either (Int, [String]) [r]

type Grammar g s = g (Parser g s)

instance (Show s, Show r) => Show (ResultList g s r) where
   show (Parsed l) = "Parsed (" ++ shows l ")"
   show (NoParse l) = "NoParse (" ++ shows l ")"

instance (Show s, Show r) => Show (ResultInfo g s r) where
   show (ResultInfo t r) = "(ResultInfo @" ++ show (fst $ head t) ++ " " ++ shows r ")"

instance Functor (ResultInfo g s) where
   fmap f (ResultInfo t r) = ResultInfo t (f r)

instance Functor (ResultList g s) where
   fmap f (Parsed l) = Parsed ((f <$>) <$> l)
   fmap _ (NoParse failure) = NoParse failure

instance Monoid (ResultList g s r) where
--   mempty = ResultList (Left $ FailureInfo 0 maxBound ["empty"])
   mempty = Parsed []
   rl1@(NoParse (FailureInfo s1 pos1 exp1)) `mappend` rl2@(NoParse (FailureInfo s2 pos2 exp2))
      | s1 < s2 = rl2
      | s1 > s2 = rl1
      | otherwise = NoParse (FailureInfo s1 pos' exp')
      where (pos', exp') | pos1 < pos2 = (pos1, exp1)
                         | pos1 > pos2 = (pos2, exp2)
                         | otherwise = (pos1, exp1 <> exp2)
   Parsed [] `mappend` rl = rl
   rl `mappend` Parsed [] = rl
   NoParse{} `mappend` rl = rl
   rl `mappend` NoParse{} = rl
   Parsed a `mappend` Parsed b = Parsed (a `mappend` b)

instance Functor (Parser g i) where
   fmap f (Parser p) = Parser (fmap f . p)

instance Applicative (Parser g i) where
   pure a = Parser (\rest-> Parsed [ResultInfo rest a])
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of Parsed results -> foldMap continue results
                  NoParse failure -> NoParse failure
      continue (ResultInfo rest' f) = f <$> q rest'


instance Alternative (Parser g i) where
   empty = Parser (\rest-> NoParse $ FailureInfo 0 (genericLength rest) ["empty"])
   Parser p <|> Parser q = Parser r where
      r rest = p rest <> q rest

infixl 3 <<|>
(<<|>) :: Parser g s r -> Parser g s r -> Parser g s r
Parser p <<|> Parser q = Parser r
   where r rest = case (p rest, q rest)
                  of (r1@NoParse{}, r2@NoParse{}) -> r1 <> r2
                     (NoParse{}, r2) -> r2
                     (Parsed [], r2) -> r2
                     (r1, _) -> r1

instance Monad (Parser g i) where
   return = pure
   Parser p >>= f = Parser q where
      q rest = case p rest
               of Parsed results -> foldMap continue results
                  NoParse failure -> NoParse failure
      continue (ResultInfo rest' a) = applyParser (f a) rest'

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance MonoidNull s => Parsing (Parser g s) where
   try (Parser p) = Parser (weakenResults . p)
      where weaken (FailureInfo s pos msgs) = FailureInfo (pred s) pos msgs
            weakenResults (NoParse err) = NoParse (weaken err)
            weakenResults rl = rl
   Parser p <?> msg  = Parser (strengthenResults . p)
      where strengthen (FailureInfo s pos _msgs) = FailureInfo (succ s) pos [msg]
            strengthenResults (NoParse err) = NoParse (strengthen err)
            strengthenResults rl = rl
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t Parsed{} = NoParse (FailureInfo 1 (genericLength t) ["notFollowedBy"])
            rewind t NoParse{} = Parsed [ResultInfo t ()]
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = Parser (\t-> NoParse $ FailureInfo 0 (genericLength t) [msg])
   eof = endOfInput

instance MonoidNull s => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind _ rl@NoParse{} = rl
            rewind t (Parsed rl) = Parsed (rewindInput t <$> rl)
            rewindInput t (ResultInfo _ r) = ResultInfo t r

instance (Show s, TextualMonoid s) => Text.Parser.Char.CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Show s, TextualMonoid s) => TokenParsing (Parser g s) where
   someSpace = () <$ takeCharsWhile1 isSpace

fromResultList :: FactorialMonoid s => s -> ResultList g s r -> ParseResults (r, s)
fromResultList s (NoParse (FailureInfo _ pos msgs)) = Left (length s - fromIntegral pos, nub msgs)
fromResultList _ (Parsed rl) = Right (f <$> rl)
   where f (ResultInfo ((s, _):_) r) = (r, s)
         f (ResultInfo [] r) = (r, mempty)

-- | Consume all whitespace characters.
whiteSpace :: forall g s. TextualMonoid s => Parser g s ()
whiteSpace = () <$ takeCharsWhile isSpace

-- | A parser that fails on any input and succeeds at its end.
endOfInput :: (MonoidNull s) => Parser g s ()
endOfInput = Parser f
   where f input@((s, _):t)
            | null s = Parsed [ResultInfo input ()]
            | otherwise = NoParse (FailureInfo 1 (genericLength t) ["endOfInput"])
         f [] = Parsed [ResultInfo [] ()]

-- | Always sucessful parser that returns the remaining input without consuming it.
getInput :: Monoid s => Parser g s s
getInput = Parser p
   where p rest@((s, _):_) = Parsed [ResultInfo [last rest] s]
         p [] = Parsed [ResultInfo [] mempty]

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeWhile :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
takeWhile predicate = Parser p
   where p rest@((s, _) : _)
            | x <- Factorial.takeWhile predicate s = Parsed [ResultInfo (Factorial.drop (Factorial.length x) rest) x]
         p [] = Parsed [ResultInfo [] mempty]

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
takeWhile1 predicate = Parser p
   where p rest@((s, _) : _)
            | x <- Factorial.takeWhile predicate s, not (null x) =
                 Parsed [ResultInfo (Factorial.drop (Factorial.length x) rest) x]
         p rest = NoParse (FailureInfo 1 (genericLength rest) ["takeWhile1"])

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeCharsWhile :: (TextualMonoid s) => (Char -> Bool) -> Parser g s s
takeCharsWhile predicate = Parser p
   where p rest@((s, _) : _)
            | x <- Textual.takeWhile_ False predicate s =
                 Parsed [ResultInfo (Factorial.drop (Factorial.length x) rest) x]
         p [] = Parsed [ResultInfo [] mempty]

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s) => (Char -> Bool) -> Parser g s s
takeCharsWhile1 predicate = Parser p
   where p rest@((s, _) : _)
            | x <- Textual.takeWhile_ False predicate s, not (null x) =
                 Parsed [ResultInfo (Factorial.drop (Factorial.length x) rest) x]
         p rest = NoParse (FailureInfo 1 (genericLength rest) ["takeCharsWhile1"])

-- | A stateful scanner.  The predicate consumes and transforms a state argument, and each transformed state is passed
-- to successive invocations of the predicate on each token of the input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first prime
-- input factor.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scan :: (FactorialMonoid t) => s -> (s -> t -> Maybe s) -> Parser g t t
scan s0 f = Parser (p s0)
   where p s ((i, _):t) = Parsed [ResultInfo (drop (length prefix - 1) t) prefix]
            where (prefix, _, _) = Factorial.spanMaybe' s f i
         p _ [] = Parsed [ResultInfo [] mempty]

-- | A stateful scanner.  The predicate consumes and transforms a
-- state argument, and each transformed state is passed to successive invocations of the predicate on each token of the
-- input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first character.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scanChars :: (TextualMonoid t) => s -> (s -> Char -> Maybe s) -> Parser g t t
scanChars s0 f = Parser (p s0)
   where p s ((i, _):t) = Parsed [ResultInfo (drop (length prefix - 1) t) prefix]
            where (prefix, _, _) = Textual.spanMaybe_' s f i
         p _ [] = Parsed [ResultInfo [] mempty]

-- | A parser that accepts any single input atom.
anyToken :: (FactorialMonoid s) => Parser g s s
anyToken = Parser p
   where p rest@((s, _):t) = case splitPrimePrefix s
                             of Just (first, _) -> Parsed [ResultInfo t first]
                                _ -> NoParse (FailureInfo 1 (genericLength rest) ["anyToken"])
         p [] = NoParse (FailureInfo 1 0 ["anyToken"])

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s) => s -> Parser g s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
satisfy predicate = Parser p
   where p rest@((s, _):t) =
            case splitPrimePrefix s
            of Just (first, _) | predicate first -> Parsed [ResultInfo t first]
               _ -> NoParse (FailureInfo 1 (genericLength rest) ["satisfy"])
         p [] = NoParse (FailureInfo 1 0 ["satisfy"])

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: (TextualMonoid s) => (Char -> Bool) -> Parser g s Char
satisfyChar predicate = Parser p
   where p rest@((s, _):t) =
            case Textual.splitCharacterPrefix s
            of Just (first, _) | predicate first -> Parsed [ResultInfo t first]
               _ -> NoParse (FailureInfo 1 (genericLength rest) ["satisfy"])
         p [] = NoParse (FailureInfo 1 0 ["satisfyChar"])

-- | A parser that consumes and returns the given prefix of the input.
string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s) => s -> Parser g s s
string s = Parser p where
   p rest@((s', _) : _)
      | s `isPrefixOf` s' = Parsed [ResultInfo (Factorial.drop (Factorial.length s) rest) s]
   p rest = NoParse (FailureInfo 1 (genericLength rest) ["string " ++ show s])
