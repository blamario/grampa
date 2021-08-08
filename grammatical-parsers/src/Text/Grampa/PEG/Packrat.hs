{-# LANGUAGE CPP, TypeFamilies, UndecidableInstances #-}
-- | Packrat parser
module Text.Grampa.PEG.Packrat (Parser(..), Result(..)) where

import Control.Applicative (Applicative(..), Alternative(..), liftA2)
import Control.Monad (Monad(..), MonadPlus(..))
#if MIN_VERSION_base(4,13,0)
import Control.Monad (MonadFail(fail))
#endif

import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (genericLength, nub)
import Data.Monoid (Monoid(mappend, mempty))
import Data.Monoid.Factorial(FactorialMonoid)
import Data.Monoid.Textual(TextualMonoid)
import Data.Semigroup (Semigroup(..))
import Data.Semigroup.Cancellative (LeftReductive(isPrefixOf))
import Data.String (fromString)
import Debug.Trace (trace)
import Witherable (Filterable(mapMaybe))

import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Null as Null
import qualified Data.Monoid.Textual as Textual

import qualified Rank2

import qualified Text.Parser.Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))
import Text.Parser.Input.Position (fromEnd)
import Text.Grampa.Class (CommittedParsing(..), DeterministicParsing(..),
                          InputParsing(..), InputCharParsing(..),
                          GrammarParsing(..), MultiParsing(..),
                          TailsParsing(parseTails), ParseResults, ParseFailure(..), Expected(..), Pos)
import Text.Grampa.Internal (TraceableParsing(..))

data Result g s v = Parsed{parsedPrefix :: !v, 
                           parsedSuffix :: ![(s, g (Result g s))]}
                  | NoParse (ParseFailure Pos s)

-- | Parser type for Parsing Expression Grammars that uses an improved packrat algorithm, with O(1) performance bounds
-- but with worse constants and more memory consumption than the backtracking 'Text.Grampa.PEG.Backtrack.Parser'. The
-- 'parse' function returns an input prefix parse paired with the remaining input suffix.
newtype Parser g s r = Parser{applyParser :: [(s, g (Result g s))] -> Result g s r}

instance Show s => Show1 (Result g s) where
   liftShowsPrec showsPrecSub _showList prec Parsed{parsedPrefix= r} rest = "Parsed " ++ showsPrecSub prec r rest
   liftShowsPrec _showsPrec _showList _prec (NoParse f) rest = "NoParse " ++ shows f rest

instance Functor (Result g s) where
   fmap f (Parsed a rest) = Parsed (f a) rest
   fmap _ (NoParse failure) = NoParse failure

instance Filterable (Result g s) where
   mapMaybe f (Parsed a rest) =
      maybe (NoParse $ ParseFailure (fromEnd $ Factorial.length rest) [Expected "filter"]) (`Parsed` rest) (f a)
   mapMaybe _ (NoParse failure) = NoParse failure
   
instance Functor (Parser g s) where
   fmap f (Parser p) = Parser (fmap f . p)

instance Applicative (Parser g s) where
   pure a = Parser (Parsed a)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of Parsed f rest' -> f <$> q rest'
                  NoParse failure -> NoParse failure

instance Alternative (Parser g s) where
   empty = Parser (\rest-> NoParse $ ParseFailure (genericLength rest) [Expected "empty"])
   Parser p <|> Parser q = Parser r where
      r rest = case p rest
               of x@Parsed{} -> x
                  NoParse{} -> q rest
   
instance Filterable (Parser g s) where
   mapMaybe f (Parser p) = Parser (mapMaybe f . p)
   {-# INLINABLE mapMaybe #-}

instance Monad (Parser g s) where
   return = pure
   Parser p >>= f = Parser r where
      r rest = case p rest
               of Parsed a rest' -> applyParser (f a) rest'
                  NoParse failure -> NoParse failure

#if MIN_VERSION_base(4,13,0)
instance MonadFail (Parser g s) where
#endif
   fail msg = Parser (\rest-> NoParse $ ParseFailure (genericLength rest) [Expected msg])

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Semigroup x => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance FactorialMonoid s => Parsing (Parser g s) where
   try (Parser p) = Parser q
      where q rest = rewindFailure (p rest)
               where rewindFailure (NoParse (ParseFailure _pos _msgs)) = NoParse (ParseFailure (genericLength rest) [])
                     rewindFailure parsed = parsed
   Parser p <?> msg  = Parser q
      where q rest = replaceFailure (p rest)
               where replaceFailure (NoParse (ParseFailure pos msgs)) =
                        NoParse (ParseFailure pos $ if pos == genericLength rest then [Expected msg] else msgs)
                     replaceFailure parsed = parsed
   eof = Parser p
      where p rest@((s, _) : _)
               | not (Null.null s) = NoParse (ParseFailure (genericLength rest) [Expected "end of input"])
            p rest = Parsed () rest
   unexpected msg = Parser (\t-> NoParse $ ParseFailure (genericLength t) [Expected msg])
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t Parsed{} = NoParse (ParseFailure (genericLength t) [Expected "notFollowedBy"])
            rewind t NoParse{} = Parsed () t

instance FactorialMonoid s => CommittedParsing (Parser g s) where
   type CommittedResults (Parser g s) = ParseResults s
   commit (Parser p) = Parser q
      where q rest = case p rest
                     of NoParse failure -> Parsed (Left failure) rest
                        Parsed a rest' -> Parsed (Right a) rest'
   admit (Parser p) = Parser q
      where q rest = case p rest
                     of NoParse failure -> NoParse failure
                        Parsed (Left failure) _ -> NoParse failure
                        Parsed (Right a) rest' -> Parsed a rest'

-- | Every PEG parser is deterministic all the time.
instance FactorialMonoid s => DeterministicParsing (Parser g s) where
   (<<|>) = (<|>)
   takeSome = some
   takeMany = many
   skipAll = skipMany

instance FactorialMonoid s => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (Parsed r _) = Parsed r t
            rewind _ r@NoParse{} = r

instance (Show s, Textual.TextualMonoid s) => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> Parsed first t
                  _ -> NoParse (ParseFailure (genericLength rest) [Expected "Char.satisfy"])
            p [] = NoParse (ParseFailure 0 [Expected "Char.satisfy"])
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

-- | Packrat parser
instance (Eq s, LeftReductive s, FactorialMonoid s) => GrammarParsing (Parser g s) where
   type ParserGrammar (Parser g s) = g
   type GrammarFunctor (Parser g s) = Result g s
   parsingResult = fromResult
   nonTerminal f = Parser p where
      p ((_, d) : _) = f d
      p _ = NoParse (ParseFailure 0 [Expected "NonTerminal at endOfInput"])

instance (Eq s, LeftReductive s, FactorialMonoid s) => TailsParsing (Parser g s) where
   parseTails = applyParser

instance (LeftReductive s, FactorialMonoid s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   getInput = Parser p
      where p rest@((s, _):_) = Parsed s rest
            p [] = Parsed mempty []
   anyToken = Parser p
      where p rest@((s, _):t) = case Factorial.splitPrimePrefix s
                                of Just (first, _) -> Parsed first t
                                   _ -> NoParse (ParseFailure (genericLength rest) [Expected "anyToken"])
            p [] = NoParse (ParseFailure 0 [Expected "anyToken"])
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case Factorial.splitPrimePrefix s
               of Just (first, _) | predicate first -> Parsed first t
                  _ -> NoParse (ParseFailure (genericLength rest) [Expected "satisfy"])
            p [] = NoParse (ParseFailure 0 [Expected "satisfy"])
   notSatisfy predicate = Parser p
      where p rest@((s, _):_)
               | Just (first, _) <- Factorial.splitPrimePrefix s, 
                 predicate first = NoParse (ParseFailure (genericLength rest) [Expected "notSatisfy"])
            p rest = Parsed () rest
   scan s0 f = Parser (p s0)
      where p s ((i, _):t) = Parsed prefix (drop (Factorial.length prefix - 1) t)
               where (prefix, _, _) = Factorial.spanMaybe' s f i
            p _ [] = Parsed mempty []
   takeWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s = Parsed x (Factorial.drop (Factorial.length x) rest)
            p [] = Parsed mempty []
   take n = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.take n s, Factorial.length x == n = Parsed x (drop n rest)
            p [] | n == 0 = Parsed mempty []
            p rest = NoParse (ParseFailure (genericLength rest) [Expected $ "take " ++ show n])
   takeWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, not (Null.null x) =
                    Parsed x (Factorial.drop (Factorial.length x) rest)
            p rest = NoParse (ParseFailure (genericLength rest) [Expected "takeWhile1"])
   string s = Parser p where
      p rest@((s', _) : _)
         | s `isPrefixOf` s' = Parsed s (Factorial.drop (Factorial.length s) rest)
      p rest = NoParse (ParseFailure (genericLength rest) [ExpectedInput s])

instance (InputParsing (Parser g s), Monoid s)  => TraceableParsing (Parser g s) where
   traceInput description (Parser p) = Parser q
      where q rest = case traceWith "Parsing " (p rest)
                  of r@Parsed{} -> traceWith "Parsed " r
                     r@NoParse{} -> traceWith "Failed " r
               where traceWith prefix = trace (prefix <> description (case rest
                                                                      of ((s, _):_) -> s
                                                                         [] -> mempty))

instance (Show s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyCharInput predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> Parsed (Factorial.primePrefix s) t
                  _ -> NoParse (ParseFailure (genericLength rest) [Expected "satisfyCharInput"])
            p [] = NoParse (ParseFailure 0 [Expected "satisfyCharInput"])
   notSatisfyChar predicate = Parser p
      where p rest@((s, _):_)
               | Just first <- Textual.characterPrefix s, 
                 predicate first = NoParse (ParseFailure (genericLength rest) [Expected "notSatisfyChar"])
            p rest = Parsed () rest
   scanChars s0 f = Parser (p s0)
      where p s ((i, _):t) = Parsed prefix (drop (Factorial.length prefix - 1) t)
               where (prefix, _, _) = Textual.spanMaybe_' s f i
            p _ [] = Parsed mempty []
   takeCharsWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s =
                    Parsed x (Factorial.drop (Factorial.length x) rest)
            p [] = Parsed mempty []
   takeCharsWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, not (Null.null x) =
                    Parsed x (drop (Factorial.length x) rest)
            p rest = NoParse (ParseFailure (genericLength rest) [Expected "takeCharsWhile1"])

-- | Packrat parser
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Packrat.'Parser' g s) -> s -> g ('ParseResults' s)
-- @
instance (LeftReductive s, FactorialMonoid s) => MultiParsing (Parser g s) where
   type ResultFunctor (Parser g s) = ParseResults s
   type GrammarConstraint (Parser g s) g' = (g ~ g', Rank2.Functor g)
   {-# NOINLINE parsePrefix #-}
   parsePrefix g input = Rank2.fmap (Compose . fromResult input) (snd $ head $ parseGrammarTails g input)
   parseComplete g input = Rank2.fmap ((snd <$>) . fromResult input)
                                      (snd $ head $ reparseTails close $ parseGrammarTails g input)
      where close = Rank2.fmap (<* eof) g

parseGrammarTails :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> [(s, g (Result g s))]
parseGrammarTails g input = foldr parseTail [] (Factorial.tails input)
      where parseTail s parsedTail = parsed where
               parsed = (s,d):parsedTail
               d      = Rank2.fmap (($ parsed) . applyParser) g

reparseTails :: Rank2.Functor g => g (Parser g s) -> [(s, g (Result g s))] -> [(s, g (Result g s))]
reparseTails _ [] = []
reparseTails final parsed@((s, _):_) = (s, gd):parsed
   where gd = Rank2.fmap (`applyParser` parsed) final

fromResult :: (Eq s, FactorialMonoid s) => s -> Result g s r -> ParseResults s (s, r)
fromResult s (NoParse (ParseFailure pos msgs)) = Left (ParseFailure (fromIntegral $ pos - 1) (nub msgs))
fromResult _ (Parsed prefix []) = Right (mempty, prefix)
fromResult _ (Parsed prefix ((s, _):_)) = Right (s, prefix)
