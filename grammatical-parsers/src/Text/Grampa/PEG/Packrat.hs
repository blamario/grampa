{-# LANGUAGE TypeFamilies, UndecidableInstances #-}
-- | Packrat parser
module Text.Grampa.PEG.Packrat (Parser(..), Result(..)) where

import Control.Applicative (Applicative(..), Alternative(..), liftA2)
import Control.Monad (Monad(..), MonadPlus(..))

import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (genericLength, nub)
import Data.Semigroup (Semigroup(..))
import Data.Monoid (Monoid(mappend, mempty))
import Data.Monoid.Factorial(FactorialMonoid)
import Data.Monoid.Textual(TextualMonoid)
import Data.String (fromString)

import qualified Data.Monoid.Cancellative as Cancellative
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
import Text.Grampa.Class (Lexical(..), GrammarParsing(..), MonoidParsing(..), MultiParsing(..), 
                          ParseResults, ParseFailure(..))
import Text.Grampa.Internal (FailureInfo(..))
import qualified Text.Grampa.PEG.Backtrack as Backtrack (Parser)

data Result g s v = Parsed{parsedPrefix :: !v, 
                           parsedSuffix :: ![(s, g (Result g s))]}
                  | NoParse FailureInfo

-- | Parser type for Parsing Expression Grammars that uses an improved packrat algorithm, with O(1) performance bounds
-- but with worse constants and more memory consumption than 'Backtrack.Parser'. The 'parse' function returns an input
-- prefix parse paired with the remaining input suffix.
newtype Parser g s r = Parser{applyParser :: [(s, g (Result g s))] -> Result g s r}

instance Show1 (Result g s) where
   liftShowsPrec showsPrecSub _showList prec Parsed{parsedPrefix= r} rest = "Parsed " ++ showsPrecSub prec r rest
   liftShowsPrec _showsPrec _showList _prec (NoParse f) rest = "NoParse " ++ shows f rest

instance Functor (Result g s) where
   fmap f (Parsed a rest) = Parsed (f a) rest
   fmap _ (NoParse failure) = NoParse failure
   
instance Functor (Parser g s) where
   fmap f (Parser p) = Parser (fmap f . p)

instance Applicative (Parser g s) where
   pure a = Parser (Parsed a)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of Parsed f rest' -> f <$> q rest'
                  NoParse failure -> NoParse failure

instance Alternative (Parser g s) where
   empty = Parser (\rest-> NoParse $ FailureInfo 0 (genericLength rest) ["empty"])
   Parser p <|> Parser q = Parser r where
      r rest = case p rest
               of x@Parsed{} -> x
                  NoParse{} -> q rest

instance Monad (Parser g s) where
   return = pure
   Parser p >>= f = Parser r where
      r rest = case p rest
               of Parsed a rest' -> applyParser (f a) rest'
                  NoParse failure -> NoParse failure

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Semigroup x => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance Factorial.FactorialMonoid s => Parsing (Parser g s) where
   try = id
   (<?>) = const
   eof = endOfInput
   unexpected msg = Parser (\t-> NoParse $ FailureInfo 0 (genericLength t) [msg])
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t Parsed{} = NoParse (FailureInfo 1 (genericLength t) ["notFollowedBy"])
            rewind t NoParse{} = Parsed () t

instance Factorial.FactorialMonoid s => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (Parsed r _) = Parsed r t
            rewind _ r@NoParse{} = r

instance (Show s, Textual.TextualMonoid s) => CharParsing (Parser g s) where
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

instance GrammarParsing Parser where
   type GrammarFunctor Parser = Result
   nonTerminal f = Parser p where
      p ((_, d) : _) = f d
      p _ = NoParse (FailureInfo 1 0 ["NonTerminal at endOfInput"])

instance MonoidParsing (Parser g) where
   endOfInput = Parser p
      where p rest@((s, _) : _)
               | not (Null.null s) = NoParse (FailureInfo 1 (genericLength rest) ["endOfInput"])
            p rest = Parsed () rest
   getInput = Parser p
      where p rest@((s, _):_) = Parsed s [last rest]
            p [] = Parsed mempty []
   anyToken = Parser p
      where p rest@((s, _):t) = case Factorial.splitPrimePrefix s
                                of Just (first, _) -> Parsed first t
                                   _ -> NoParse (FailureInfo 1 (genericLength rest) ["anyToken"])
            p [] = NoParse (FailureInfo 1 0 ["anyToken"])
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case Factorial.splitPrimePrefix s
               of Just (first, _) | predicate first -> Parsed first t
                  _ -> NoParse (FailureInfo 1 (genericLength rest) ["satisfy"])
            p [] = NoParse (FailureInfo 1 0 ["satisfy"])
   satisfyChar predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> Parsed first t
                  _ -> NoParse (FailureInfo 1 (genericLength rest) ["satisfyChar"])
            p [] = NoParse (FailureInfo 1 0 ["satisfyChar"])
   satisfyCharInput predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> Parsed (Factorial.primePrefix s) t
                  _ -> NoParse (FailureInfo 1 (genericLength rest) ["satisfyChar"])
            p [] = NoParse (FailureInfo 1 0 ["satisfyChar"])
   notSatisfy predicate = Parser p
      where p rest@((s, _):_)
               | Just (first, _) <- Factorial.splitPrimePrefix s, 
                 predicate first = NoParse (FailureInfo 1 (genericLength rest) ["notSatisfy"])
            p rest = Parsed () rest
   notSatisfyChar predicate = Parser p
      where p rest@((s, _):_)
               | Just first <- Textual.characterPrefix s, 
                 predicate first = NoParse (FailureInfo 1 (genericLength rest) ["notSatisfyChar"])
            p rest = Parsed () rest
   scan s0 f = Parser (p s0)
      where p s ((i, _):t) = Parsed prefix (drop (Factorial.length prefix - 1) t)
               where (prefix, _, _) = Factorial.spanMaybe' s f i
            p _ [] = Parsed mempty []
   scanChars s0 f = Parser (p s0)
      where p s ((i, _):t) = Parsed prefix (drop (Factorial.length prefix - 1) t)
               where (prefix, _, _) = Textual.spanMaybe_' s f i
            p _ [] = Parsed mempty []
   takeWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s = Parsed x (Factorial.drop (Factorial.length x) rest)
            p [] = Parsed mempty []
   takeWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, not (Null.null x) =
                    Parsed x (Factorial.drop (Factorial.length x) rest)
            p rest = NoParse (FailureInfo 1 (genericLength rest) ["takeWhile1"])
   takeCharsWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s =
                    Parsed x (Factorial.drop (Factorial.length x) rest)
            p [] = Parsed mempty []
   takeCharsWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, not (Null.null x) =
                    Parsed x (drop (Factorial.length x) rest)
            p rest = NoParse (FailureInfo 1 (genericLength rest) ["takeCharsWhile1"])
   string s = Parser p where
      p rest@((s', _) : _)
         | Cancellative.isPrefixOf s s' = Parsed s (Factorial.drop (Factorial.length s) rest)
      p rest = NoParse (FailureInfo 1 (genericLength rest) ["string " ++ show s])
   concatMany p = go
      where go = mappend <$> p <*> go <|> mempty


-- | Packrat parser
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Packrat.'Parser' g s) -> s -> g 'ParseResults'
-- @
instance MultiParsing Parser where
   type ResultFunctor Parser = ParseResults
   {-# NOINLINE parsePrefix #-}
   parsePrefix g input = Rank2.fmap (Compose . fromResult input) (snd $ head $ parseTails g input)
   parseComplete g input = Rank2.fmap ((snd <$>) . fromResult input)
                                      (snd $ head $ reparseTails close $ parseTails g input)
      where close = Rank2.fmap (<* endOfInput) g

parseTails :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> [(s, g (Result g s))]
parseTails g input = foldr parseTail [] (Factorial.tails input)
      where parseTail s parsedTail = parsed where
               parsed = (s,d):parsedTail
               d      = Rank2.fmap (($ parsed) . applyParser) g

reparseTails :: Rank2.Functor g => g (Parser g s) -> [(s, g (Result g s))] -> [(s, g (Result g s))]
reparseTails _ [] = []
reparseTails final parsed@((s, _):_) = (s, gd):parsed
   where gd = Rank2.fmap (`applyParser` parsed) final

fromResult :: FactorialMonoid s => s -> Result g s r -> ParseResults (s, r)
fromResult s (NoParse (FailureInfo _ pos msgs)) =
   Left (ParseFailure (Factorial.length s - fromIntegral pos + 1) (nub msgs))
fromResult _ (Parsed prefix []) = Right (mempty, prefix)
fromResult _ (Parsed prefix ((s, _):_)) = Right (s, prefix)
