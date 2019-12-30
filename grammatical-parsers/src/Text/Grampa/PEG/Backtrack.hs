{-# LANGUAGE TypeFamilies, UndecidableInstances #-}
-- | Backtracking parser for Parsing Expression Grammars
module Text.Grampa.PEG.Backtrack (Parser(..), Result(..), alt) where

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

-- | Parser type for Parsing Expression Grammars that uses a backtracking algorithm, fast for grammars in LL(1) class
-- but with potentially exponential performance for longer ambiguous prefixes.
newtype Parser g s r = Parser{applyParser :: s -> Result g s r}

instance Show s => Show1 (Result g s) where
   liftShowsPrec showsPrecSub _showList prec Parsed{parsedPrefix= r} rest = "Parsed " ++ showsPrecSub prec r rest
   liftShowsPrec _showsPrec _showList _prec (NoParse f) rest = "NoParse " ++ shows f rest

instance Functor (Result g s) where
   fmap f (Parsed a rest) = Parsed (f a) rest
   fmap _ (NoParse failure) = NoParse failure
   
instance Functor (Parser g s) where
   fmap f (Parser p) = Parser (fmap f . p)
   {-# INLINABLE fmap #-}

instance Applicative (Parser g s) where
   pure a = Parser (Parsed a)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of Parsed f rest' -> f <$> q rest'
                  NoParse failure -> NoParse failure
   {-# INLINABLE (<*>) #-}

instance Factorial.FactorialMonoid s => Alternative (Parser g s) where
   empty = Parser (\rest-> NoParse $ FailureInfo (Factorial.length rest) [Expected "empty"])
   (<|>) = alt

-- | A named and unconstrained version of the '<|>' operator
alt :: Parser g s a -> Parser g s a -> Parser g s a
Parser p `alt` Parser q = Parser r where
      r rest = case p rest
               of x@Parsed{} -> x
                  NoParse{} -> q rest

instance Monad (Parser g s) where
   return = pure
   Parser p >>= f = Parser r where
      r rest = case p rest
               of Parsed a rest' -> applyParser (f a) rest'
                  NoParse failure -> NoParse failure

instance Factorial.FactorialMonoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Semigroup x => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance Factorial.FactorialMonoid s => Parsing (Parser g s) where
   try (Parser p) = Parser q
      where q rest = rewindFailure (p rest)
               where rewindFailure (NoParse (FailureInfo _pos _msgs)) =
                        NoParse (FailureInfo (Factorial.length rest) [])
                     rewindFailure parsed = parsed
   Parser p <?> msg  = Parser q
      where q rest = replaceFailure (p rest)
               where replaceFailure (NoParse (FailureInfo pos msgs)) =
                        NoParse (FailureInfo pos $ if pos == Factorial.length rest then [Expected msg] else msgs)
                     replaceFailure parsed = parsed
   eof = Parser p
      where p rest
               | Null.null rest = Parsed () rest
               | otherwise = NoParse (FailureInfo (Factorial.length rest) [Expected "end of input"])
   unexpected msg = Parser (\t-> NoParse $ FailureInfo (Factorial.length t) [Expected msg])
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t Parsed{} = NoParse (FailureInfo (Factorial.length t) [Expected "notFollowedBy"])
            rewind t NoParse{} = Parsed () t

instance Factorial.FactorialMonoid s => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (Parsed r _) = Parsed r t
            rewind _ r@NoParse{} = r

instance (Show s, Textual.TextualMonoid s) => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p rest =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> Parsed first suffix
                  _ -> NoParse (FailureInfo (Factorial.length rest) [Expected "Char.satisfy"])
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Lexical g, LexicalConstraint Parser g s, Show s, TextualMonoid s) => TokenParsing (Parser g s) where
   someSpace = someLexicalSpace
   semi = lexicalSemicolon
   token = lexicalToken

instance (Cancellative.LeftReductive s, FactorialMonoid s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   endOfInput = eof
   getInput = Parser p
      where p rest = Parsed rest rest
   anyToken = Parser p
      where p rest = case Factorial.splitPrimePrefix rest
                     of Just (first, suffix) -> Parsed first suffix
                        _ -> NoParse (FailureInfo (Factorial.length rest) [Expected "anyToken"])
   satisfy predicate = Parser p
      where p rest =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) | predicate first -> Parsed first suffix
                  _ -> NoParse (FailureInfo (Factorial.length rest) [Expected "satisfy"])
   notSatisfy predicate = Parser p
      where p s = case Factorial.splitPrimePrefix s
                  of Just (first, _) 
                        | predicate first -> NoParse (FailureInfo (Factorial.length s) [Expected "notSatisfy"])
                     _ -> Parsed () s
   scan s0 f = Parser (p s0)
      where p s rest = Parsed prefix suffix
               where (prefix, suffix, _) = Factorial.spanMaybe' s f rest
   takeWhile predicate = Parser p
      where p rest | (prefix, suffix) <- Factorial.span predicate rest = Parsed prefix suffix
   takeWhile1 predicate = Parser p
      where p rest | (prefix, suffix) <- Factorial.span predicate rest =
                        if Null.null prefix
                        then NoParse (FailureInfo (Factorial.length rest) [Expected "takeWhile1"])
                        else Parsed prefix suffix
   string s = Parser p where
      p s' | Just suffix <- Cancellative.stripPrefix s s' = Parsed s suffix
           | otherwise = NoParse (FailureInfo (Factorial.length s') [ExpectedInput s])
   concatMany (Parser p) = Parser q
      where q rest = case p rest
                     of Parsed prefix suffix -> let Parsed prefix' suffix' = q suffix
                                                in Parsed (mappend prefix prefix') suffix'
                        NoParse{} -> Parsed mempty rest
   {-# INLINABLE string #-}

instance (Show s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyChar predicate = Parser p
      where p rest =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> Parsed first suffix
                  _ -> NoParse (FailureInfo (Factorial.length rest) [Expected "satisfyChar"])
   satisfyCharInput predicate = Parser p
      where p rest =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> Parsed (Factorial.primePrefix rest) suffix
                  _ -> NoParse (FailureInfo (Factorial.length rest) [Expected "satisfyCharInput"])
   notSatisfyChar predicate = Parser p
      where p s = case Textual.characterPrefix s
                  of Just first | predicate first 
                                  -> NoParse (FailureInfo (Factorial.length s) [Expected "notSatisfyChar"])
                     _ -> Parsed () s
   scanChars s0 f = Parser (p s0)
      where p s rest = Parsed prefix suffix
               where (prefix, suffix, _) = Textual.spanMaybe_' s f rest
   takeCharsWhile predicate = Parser p
      where p rest | (prefix, suffix) <- Textual.span_ False predicate rest = Parsed prefix suffix
   takeCharsWhile1 predicate = Parser p
      where p rest | (prefix, suffix) <- Textual.span_ False predicate rest =
                     if Null.null prefix
                     then NoParse (FailureInfo (Factorial.length rest) [Expected "takeCharsWhile1"])
                     else Parsed prefix suffix

-- | Backtracking PEG parser
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Backtrack.'Parser' g s) -> s -> g ('ParseResults' s)
-- @
instance MultiParsing Parser where
   type ResultFunctor Parser s = ParseResults s
   {-# NOINLINE parsePrefix #-}
   -- | Returns an input prefix parse paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . fromResult input . (`applyParser` input)) g
   parseComplete g input = Rank2.fmap ((snd <$>) . fromResult input . (`applyParser` input))
                                      (Rank2.fmap (<* eof) g)

fromResult :: (Eq s, FactorialMonoid s) => s -> Result g s r -> ParseResults s (s, r)
fromResult s (NoParse (FailureInfo pos msgs)) =
   Left (ParseFailure (Factorial.length s - pos + 1) (nub msgs))
fromResult _ (Parsed prefix suffix) = Right (suffix, prefix)
