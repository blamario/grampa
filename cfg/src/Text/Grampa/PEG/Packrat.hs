{-# LANGUAGE TypeFamilies #-}
-- | Packrat parser
module Text.Grampa.PEG.Packrat (Parser, parse) where

import Control.Applicative (Applicative(..), Alternative(..), liftA2)
import Control.Monad (Monad(..), MonadPlus(..))

import Data.Char (isSpace)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (genericLength, nub)
import Data.Monoid (Monoid(mappend, mempty), (<>))
import Data.Monoid.Factorial(FactorialMonoid)
import Data.Word (Word64)

import qualified Data.Monoid.Cancellative as Cancellative
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Null as Null
import qualified Data.Monoid.Textual as Textual

import qualified Rank2

import Text.Parser.Combinators (Parsing(..))
import Text.Grampa.Class (GrammarParsing(..), MonoidParsing(..), ParseResults, ParseFailure(..))

data Result g s v = Parsed{parsedPrefix :: v, 
                           parsedSuffix :: [(s, g (Result g s))]}
                  | NoParse FailureInfo
data FailureInfo = FailureInfo !Int Word64 [String] deriving (Eq, Show)

-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
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

instance GrammarParsing Parser where
   type GrammarFunctor Parser = Result
   nonTerminal f = Parser p where
      p ((_, d) : _) = f d
      p _ = NoParse (FailureInfo 1 0 ["NonTerminal at endOfInput"])

instance MonoidParsing (Parser g) where
   (<<|>) = (<|>)
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
               case Textual.splitCharacterPrefix s
               of Just (first, _) | predicate first -> Parsed first t
                  _ -> NoParse (FailureInfo 1 (genericLength rest) ["satisfyChar"])
            p [] = NoParse (FailureInfo 1 0 ["satisfyChar"])
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
   whiteSpace = () <$ takeCharsWhile isSpace
   concatMany p = go
      where go = (<>) <$> p <*> go <|> mempty


{-# NOINLINE parse #-}
parse :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> g (Compose ParseResults ((,) s))
--parse :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> [(s, g (Result g s))]
parse g input = Rank2.fmap (Compose . fromResult input) (snd $ head $ foldr parseTail [] $ Factorial.tails input)
   where parseTail s parsedTail = parsed where
            parsed = (s,d):parsedTail
            d      = Rank2.fmap (($ parsed) . applyParser) g

fromResult :: FactorialMonoid s => s -> Result g s r -> ParseResults (s, r)
fromResult s (NoParse (FailureInfo _ pos msgs)) =
   Left (ParseFailure (Factorial.length s - fromIntegral pos + 1) (nub msgs))
fromResult _ (Parsed prefix []) = Right (mempty, prefix)
fromResult _ (Parsed prefix ((s, _):_)) = Right (s, prefix)
