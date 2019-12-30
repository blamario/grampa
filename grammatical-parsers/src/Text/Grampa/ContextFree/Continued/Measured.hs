{-# LANGUAGE BangPatterns, InstanceSigs, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
-- | Continuation-passing parser for context-free grammars that keeps track of the parsed prefix length
module Text.Grampa.ContextFree.Continued.Measured (Parser(..), Result(..), alt) where

import Control.Applicative (Applicative(..), Alternative(..), liftA2)
import Control.Monad (Monad(..), MonadPlus(..))

import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (nub)
import Data.Semigroup (Semigroup(..))
import Data.Monoid (Monoid(mappend, mempty))
import Data.Monoid.Factorial(FactorialMonoid)
import Data.Monoid.Textual(TextualMonoid)
import Data.String (fromString)

import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Null as Null
import qualified Data.Monoid.Textual as Textual
import qualified Data.Semigroup.Cancellative as Cancellative

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

-- | Parser type for context-free grammars that uses a continuation-passing algorithm, fast for grammars in LL(1)
-- class but with potentially exponential performance for longer ambiguous prefixes.
newtype Parser (g :: (* -> *) -> *) s r =
   Parser{applyParser :: forall x. s -> (r -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x}

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
   pure a = Parser (\input success failure-> success a 0 input failure)
   (<*>) :: forall a b. Parser g s (a -> b) -> Parser g s a -> Parser g s b
   Parser p <*> Parser q = Parser r where
      r :: forall x. s -> (b -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
      r rest success failure = p rest (\f len rest'-> q rest' (\a len'-> success (f a) $! len + len')) failure
   {-# INLINABLE (<*>) #-}

instance Factorial.FactorialMonoid s => Alternative (Parser g s) where
   empty = Parser (\rest _ failure-> failure $ FailureInfo (Factorial.length rest) [Expected "empty"])
   (<|>) = alt

-- | A named and unconstrained version of the '<|>' operator
alt :: forall g s a. Parser g s a -> Parser g s a -> Parser g s a
Parser p `alt` Parser q = Parser r where
   r :: forall x. s -> (a -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
   r rest success failure = p rest success' failure'
      where success' a len rest' _ = success a len rest' failure'
            failure' f1 = q rest success (\f2 -> failure (f1 <> f2))

instance Monad (Parser g s) where
   return = pure
   (>>=) :: forall a b. Parser g s a -> (a -> Parser g s b) -> Parser g s b
   Parser p >>= f = Parser r where
      r :: forall x. s -> (b -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
      r rest success failure = p rest
                                 (\a len rest'-> applyParser (f a) rest' $ \b len'-> success b $! len + len')
                                 failure

instance Factorial.FactorialMonoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Semigroup x => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance Factorial.FactorialMonoid s => Parsing (Parser g s) where
   try :: forall a. Parser g s a -> Parser g s a
   try (Parser p) = Parser q
      where q :: forall x. s -> (a -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            q input success failure = p input success (failure . rewindFailure)
               where rewindFailure (FailureInfo _pos _msgs) = FailureInfo (Factorial.length input) []
   (<?>) :: forall a. Parser g s a -> String -> Parser g s a
   Parser p <?> msg  = Parser q
      where q :: forall x. s -> (a -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            q input success failure = p input success (failure . replaceFailure)
               where replaceFailure (FailureInfo pos msgs) =
                        FailureInfo pos (if pos == Factorial.length input then [Expected msg] else msgs)
   eof = Parser p
      where p rest success failure
               | Null.null rest = success () 0 rest failure
               | otherwise = failure (FailureInfo (Factorial.length rest) [Expected "end of input"])
   unexpected msg = Parser (\t _ failure -> failure $ FailureInfo (Factorial.length t) [Expected msg])
   notFollowedBy (Parser p) = Parser q
      where q :: forall x. s -> (() -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            q input success failure = p input success' failure'
               where success' _ _ _ _ = failure (FailureInfo (Factorial.length input) [Expected "notFollowedBy"])
                     failure' _ = success () 0 input failure

instance Factorial.FactorialMonoid s => LookAheadParsing (Parser g s) where
   lookAhead :: forall a. Parser g s a -> Parser g s a
   lookAhead (Parser p) = Parser q
      where q :: forall x. s -> (a -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            q input success failure = p input success' failure'
               where success' a _ _ = success a 0 input
                     failure' f = failure f

instance (Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p :: forall x. s -> (Char -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> success first 1 suffix failure
                  _ -> failure (FailureInfo (Factorial.length rest) [Expected "Char.satisfy"])
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Lexical g, LexicalConstraint Parser g s, Show s, TextualMonoid s) => TokenParsing (Parser g s) where
   someSpace = someLexicalSpace
   semi = lexicalSemicolon
   token = lexicalToken

instance (Cancellative.LeftReductive s, Factorial.FactorialMonoid s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   endOfInput = eof
   getInput = Parser p
      where p rest success failure = success rest 0 rest failure
   anyToken = Parser p
      where p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) -> success first 1 suffix failure
                  _ -> failure (FailureInfo (Factorial.length rest) [Expected "anyToken"])
   satisfy predicate = Parser p
      where p :: forall x. s -> (s -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) | predicate first -> success first 1 suffix failure
                  _ -> failure (FailureInfo (Factorial.length rest) [Expected "satisfy"])
   notSatisfy predicate = Parser p
      where p :: forall x. s -> (() -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, _)
                     | predicate first -> failure (FailureInfo (Factorial.length rest) [Expected "notSatisfy"])
                  _ -> success () 0 rest failure
   scan :: forall state. state -> (state -> s -> Maybe state) -> Parser g s s
   scan s0 f = Parser (p s0)
      where p :: forall x. state -> s -> (s -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p s rest success failure = success prefix len suffix failure
               where (prefix, suffix, _) = Factorial.spanMaybe' s f rest
                     !len = Factorial.length prefix
   takeWhile predicate = Parser p
      where p :: forall x. s -> (s -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p rest success failure 
               | (prefix, suffix) <- Factorial.span predicate rest, 
                 !len <- Factorial.length prefix = 
                    success prefix len suffix failure
   takeWhile1 predicate = Parser p
      where p :: forall x. s -> (s -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p rest success failure
               | (prefix, suffix) <- Factorial.span predicate rest, 
                 !len <- Factorial.length prefix =
                    if len == 0
                    then failure (FailureInfo (Factorial.length rest) [Expected "takeWhile1"])
                    else success prefix len suffix failure
   string s = Parser p where
      p :: forall x. s -> (s -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
      p s' success failure
         | Just suffix <- Cancellative.stripPrefix s s', !len <- Factorial.length s = success s len suffix failure
         | otherwise = failure (FailureInfo (Factorial.length s') [ExpectedInput s])
   concatMany :: forall a. Monoid a => Parser g s a -> Parser g s a
   concatMany (Parser p) = Parser q
      where q :: forall x. s -> (a -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            q rest success failure = p rest success' (const $ success mempty 0 rest failure)
               where success' prefix !len suffix failure' =
                        q suffix 
                          (\prefix' !len'-> success (mappend prefix prefix') (len + len')) 
                          (const $ success prefix len suffix failure')
   {-# INLINABLE string #-}

instance (Show s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyCharInput predicate = Parser p
      where p :: forall x. s -> (s -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> success (Factorial.primePrefix rest) 1 suffix failure
                  _ -> failure (FailureInfo (Factorial.length rest) [Expected "satisfyChar"])
   notSatisfyChar predicate = Parser p
      where p :: forall x. s -> (() -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p rest success failure =
               case Textual.characterPrefix rest
               of Just first | predicate first
                               -> failure (FailureInfo (Factorial.length rest) [Expected "notSatisfyChar"])
                  _ -> success () 0 rest failure
   scanChars :: forall state. state -> (state -> Char -> Maybe state) -> Parser g s s
   scanChars s0 f = Parser (p s0)
      where p :: forall x. state -> s -> (s -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p s rest success failure = success prefix len suffix failure
               where (prefix, suffix, _) = Textual.spanMaybe_' s f rest
                     !len = Factorial.length prefix
   takeCharsWhile predicate = Parser p
      where p :: forall x. s -> (s -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p rest success failure
               | (prefix, suffix) <- Textual.span_ False predicate rest, 
                 !len <- Factorial.length prefix = success prefix len suffix failure
   takeCharsWhile1 predicate = Parser p
      where p :: forall x. s -> (s -> Int -> s -> (FailureInfo s -> x) -> x) -> (FailureInfo s -> x) -> x
            p rest success failure
               | Null.null prefix = failure (FailureInfo (Factorial.length rest) [Expected "takeCharsWhile1"])
               | otherwise = len `seq` success prefix len suffix failure
               where (prefix, suffix) = Textual.span_ False predicate rest
                     len = Factorial.length prefix

-- | Continuation-passing context-free parser that keeps track of the parsed prefix length
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Continued.'Parser' g s) -> s -> g ('ParseResults' s)
-- @
instance MultiParsing Parser where
   type ResultFunctor Parser s = ParseResults s
   -- | Returns an input prefix parse paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . (\p-> applyParser p input
                                                                 (\a _ rest _-> Right (rest, a))
                                                                 (Left . fromFailure input))) 
                                    g
   parseComplete g input = Rank2.fmap (\p-> applyParser p input
                                                        (const . const . const . Right)
                                                        (Left . fromFailure input))
                                      (Rank2.fmap (<* eof) g)

fromFailure :: (Eq s, FactorialMonoid s) => s -> FailureInfo s -> ParseFailure s
fromFailure s (FailureInfo pos msgs) = ParseFailure (Factorial.length s - pos + 1) (nub msgs)
