{-# LANGUAGE InstanceSigs, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
-- | Continuation-passing parser for Parsing Expression Grammars
module Text.Grampa.PEG.Continued (Parser(..), Result(..), alt) where

import Control.Applicative (Applicative(..), Alternative(..), liftA2)
import Control.Monad (Monad(..), MonadPlus(..))

import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (nub)
import Data.Semigroup (Semigroup((<>)))
import Data.Semigroup.Cancellative (LeftReductive(stripPrefix))
import Data.Monoid (Monoid(mappend, mempty))
import Data.Monoid.Factorial(FactorialMonoid)
import Data.Monoid.Textual(TextualMonoid)
import Data.String (fromString)

import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Null as Null
import qualified Data.Monoid.Textual as Textual

import qualified Rank2

import qualified Text.Parser.Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))
import Text.Parser.Token (TokenParsing)
import qualified Text.Parser.Token
import Text.Grampa.Class (Lexical(..), InputParsing(..), InputCharParsing(..), MultiParsing(..),
                          ParseResults, ParseFailure(..), Expected(..))
import Text.Grampa.Internal (FailureInfo(..))

data Result (g :: (* -> *) -> *) s v = Parsed{parsedPrefix :: !v,
                                              parsedSuffix :: !s}
                                     | NoParse (FailureInfo s)

-- | Parser type for Parsing Expression Grammars that uses a continuation-passing algorithm, fast for grammars in
-- LL(1) class but with potentially exponential performance for longer ambiguous prefixes.
newtype Parser (g :: (* -> *) -> *) s r =
   Parser{applyParser :: forall x. s -> (r -> s -> x) -> (FailureInfo s -> x) -> x}

instance Show s => Show1 (Result g s) where
   liftShowsPrec showsPrecSub _showList prec Parsed{parsedPrefix= r} rest = "Parsed " ++ showsPrecSub prec r rest
   liftShowsPrec _showsPrec _showList _prec (NoParse f) rest = "NoParse " ++ shows f rest

instance Functor (Result g s) where
   fmap f (Parsed a rest) = Parsed (f a) rest
   fmap _ (NoParse failure) = NoParse failure
   
instance Functor (Parser g s) where
   fmap f (Parser p) = Parser (\input success-> p input (success . f))
   {-# INLINABLE fmap #-}

instance Applicative (Parser g s) where
   pure a = Parser (\input success _-> success a input)
   (<*>) :: forall a b. Parser g s (a -> b) -> Parser g s a -> Parser g s b
   Parser p <*> Parser q = Parser r where
      r :: forall x. s -> (b -> s -> x) -> (FailureInfo s -> x) -> x
      r rest success failure = p rest (\f rest'-> q rest' (success . f) failure) failure
   {-# INLINABLE (<*>) #-}

instance FactorialMonoid s => Alternative (Parser g s) where
   empty = Parser (\rest _ failure-> failure $ FailureInfo (Factorial.length rest) [Expected "empty"])
   (<|>) = alt

-- | A named and unconstrained version of the '<|>' operator
alt :: forall g s a. Parser g s a -> Parser g s a -> Parser g s a
Parser p `alt` Parser q = Parser r where
   r :: forall x. s -> (a -> s -> x) -> (FailureInfo s -> x) -> x
   r rest success failure = p rest success (\f1-> q rest success $ \f2 -> failure (f1 <> f2))

instance Monad (Parser g s) where
   return = pure
   (>>=) :: forall a b. Parser g s a -> (a -> Parser g s b) -> Parser g s b
   Parser p >>= f = Parser r where
      r :: forall x. s -> (b -> s -> x) -> (FailureInfo s -> x) -> x
      r rest success failure = p rest (\a rest'-> applyParser (f a) rest' success failure) failure

instance FactorialMonoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Semigroup x => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance FactorialMonoid s => Parsing (Parser g s) where
   try :: forall a. Parser g s a -> Parser g s a
   try (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> x) -> (FailureInfo s -> x) -> x
            q input success failure = p input success (failure . rewindFailure)
               where rewindFailure (FailureInfo _pos _msgs) = FailureInfo (Factorial.length input) []
   (<?>) :: forall a. Parser g s a -> String -> Parser g s a
   Parser p <?> msg  = Parser q
      where q :: forall x. s -> (a -> s -> x) -> (FailureInfo s -> x) -> x
            q input success failure = p input success (failure . replaceFailure)
               where replaceFailure (FailureInfo pos msgs) =
                        FailureInfo pos (if pos == Factorial.length input then [Expected msg] else msgs)
   eof = Parser p
      where p rest success failure
               | Null.null rest = success () rest
               | otherwise = failure (FailureInfo (Factorial.length rest) [Expected "end of input"])
   unexpected msg = Parser (\t _ failure -> failure $ FailureInfo (Factorial.length t) [Expected msg])
   notFollowedBy (Parser p) = Parser q
      where q :: forall x. s -> (() -> s -> x) -> (FailureInfo s -> x) -> x
            q input success failure = p input success' failure'
               where success' _ _ = failure (FailureInfo (Factorial.length input) [Expected "notFollowedBy"])
                     failure' _ = success () input

instance FactorialMonoid s => LookAheadParsing (Parser g s) where
   lookAhead :: forall a. Parser g s a -> Parser g s a
   lookAhead (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> x) -> (FailureInfo s -> x) -> x
            q input success failure = p input success' failure'
               where success' a _ = success a input
                     failure' f = failure f

instance (Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Lexical g, LexicalConstraint Parser g s, Show s, TextualMonoid s) => TokenParsing (Parser g s) where
   someSpace = someLexicalSpace
   semi = lexicalSemicolon
   token = lexicalToken

instance (LeftReductive s, FactorialMonoid s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   endOfInput = eof
   getInput = Parser p
      where p rest success _ = success rest rest
   anyToken = Parser p
      where p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) -> success first suffix
                  _ -> failure (FailureInfo (Factorial.length rest) [Expected "anyToken"])
   satisfy predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) | predicate first -> success first suffix
                  _ -> failure (FailureInfo (Factorial.length rest) [Expected "satisfy"])
   notSatisfy predicate = Parser p
      where p :: forall x. s -> (() -> s -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, _)
                     | predicate first -> failure (FailureInfo (Factorial.length rest) [Expected "notSatisfy"])
                  _ -> success () rest
   scan :: forall state. state -> (state -> s -> Maybe state) -> Parser g s s
   scan s0 f = Parser (p s0)
      where p :: forall x. state -> s -> (s -> s -> x) -> (FailureInfo s -> x) -> x
            p s rest success _ = success prefix suffix
               where (prefix, suffix, _) = Factorial.spanMaybe' s f rest
   takeWhile predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (FailureInfo s -> x) -> x
            p rest success _ | (prefix, suffix) <- Factorial.span predicate rest = success prefix suffix
   takeWhile1 predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (FailureInfo s -> x) -> x
            p rest success failure
               | (prefix, suffix) <- Factorial.span predicate rest =
                    if Null.null prefix
                    then failure (FailureInfo (Factorial.length rest) [Expected "takeWhile1"])
                    else success prefix suffix
   string s = Parser p where
      p :: forall x. s -> (s -> s -> x) -> (FailureInfo s -> x) -> x
      p s' success failure
         | Just suffix <- stripPrefix s s' = success s suffix
         | otherwise = failure (FailureInfo (Factorial.length s') [ExpectedInput s])
   concatMany :: forall a. Monoid a => Parser g s a -> Parser g s a
   concatMany (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> x) -> (FailureInfo s -> x) -> x
            q rest success _ = p rest success' failure
               where success' prefix suffix = q suffix (success . mappend prefix) (const $ success prefix suffix)
                     failure _ = success mempty rest
   {-# INLINABLE string #-}

instance (Show s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyChar predicate = Parser p
      where p :: forall x. s -> (Char -> s -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> success first suffix
                  _ -> failure (FailureInfo (Factorial.length rest) [Expected "satisfyChar"])
   satisfyCharInput predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> success (Factorial.primePrefix rest) suffix
                  _ -> failure (FailureInfo (Factorial.length rest) [Expected "satisfyChar"])
   notSatisfyChar predicate = Parser p
      where p :: forall x. s -> (() -> s -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Textual.characterPrefix rest
               of Just first | predicate first
                               -> failure (FailureInfo (Factorial.length rest) [Expected "notSatisfyChar"])
                  _ -> success () rest
   scanChars :: forall state. state -> (state -> Char -> Maybe state) -> Parser g s s
   scanChars s0 f = Parser (p s0)
      where p :: forall x. state -> s -> (s -> s -> x) -> (FailureInfo s -> x) -> x
            p s rest success _ = success prefix suffix
               where (prefix, suffix, _) = Textual.spanMaybe_' s f rest
   takeCharsWhile predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (FailureInfo s -> x) -> x
            p rest success _ | (prefix, suffix) <- Textual.span_ False predicate rest = success prefix suffix
   takeCharsWhile1 predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (FailureInfo s -> x) -> x
            p rest success failure
               | Null.null prefix = failure (FailureInfo (Factorial.length rest) [Expected "takeCharsWhile1"])
               | otherwise = success prefix suffix
               where (prefix, suffix) = Textual.span_ False predicate rest

-- | Continuation-passing PEG parser
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Continued.'Parser' g s) -> s -> g ('ParseResults' s)
-- @
instance MultiParsing Parser where
   type ResultFunctor Parser s = ParseResults s
   -- | Returns an input prefix parse paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . (\p-> applyParser p input (flip $ curry Right) (Left . fromFailure input))) g
   parseComplete g input = Rank2.fmap (\p-> applyParser p input (const . Right) (Left . fromFailure input))
                                      (Rank2.fmap (<* eof) g)

fromFailure :: (Eq s, FactorialMonoid s) => s -> FailureInfo s -> ParseFailure s
fromFailure s (FailureInfo pos msgs) = ParseFailure (Factorial.length s - pos + 1) (nub msgs)
