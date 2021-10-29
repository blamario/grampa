{-# LANGUAGE CPP, InstanceSigs, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
-- | Continuation-passing parser for Parsing Expression Grammars
module Text.Grampa.PEG.Continued (Parser(..), Result(..), alt) where

import Control.Applicative (Applicative(..), Alternative(..), liftA2)
import Control.Monad (Monad(..), MonadPlus(..))
#if MIN_VERSION_base(4,13,0)
import Control.Monad (MonadFail(fail))
#endif

import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (nub)
import Data.Semigroup (Semigroup((<>)))
import Data.Semigroup.Cancellative (LeftReductive(stripPrefix))
import Data.Monoid (Monoid(mappend, mempty))
import Data.Monoid.Factorial(FactorialMonoid)
import Data.Monoid.Textual(TextualMonoid)
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
                          InputParsing(..), InputCharParsing(..), MultiParsing(..),
                          ParseResults, ParseFailure(..), FailureDescription(..), Pos)
import Text.Grampa.Internal (expected, TraceableParsing(..))

data Result (g :: (* -> *) -> *) s v = Parsed{parsedPrefix :: !v,
                                              parsedSuffix :: !s}
                                     | NoParse (ParseFailure Pos s)

-- | Parser type for Parsing Expression Grammars that uses a continuation-passing algorithm, fast for grammars in
-- LL(1) class but with potentially exponential performance for longer ambiguous prefixes.
newtype Parser (g :: (* -> *) -> *) s r =
   Parser{applyParser :: forall x. s -> (r -> s -> x) -> (ParseFailure Pos s -> x) -> x}

instance Show s => Show1 (Result g s) where
   liftShowsPrec showsPrecSub _showList prec Parsed{parsedPrefix= r} rest = "Parsed " ++ showsPrecSub prec r rest
   liftShowsPrec _showsPrec _showList _prec (NoParse f) rest = "NoParse " ++ shows f rest

instance Functor (Result g s) where
   fmap f (Parsed a rest) = Parsed (f a) rest
   fmap _ (NoParse failure) = NoParse failure

instance Factorial.FactorialMonoid s => Filterable (Result g s) where
   mapMaybe f (Parsed a rest) =
      maybe (NoParse $ ParseFailure (fromEnd $ Factorial.length rest) [StaticDescription "filter"] [])
            (`Parsed` rest) (f a)
   mapMaybe _ (NoParse failure) = NoParse failure
   
instance Functor (Parser g s) where
   fmap f (Parser p) = Parser (\input success-> p input (success . f))
   {-# INLINABLE fmap #-}

instance Applicative (Parser g s) where
   pure a = Parser (\input success _-> success a input)
   (<*>) :: forall a b. Parser g s (a -> b) -> Parser g s a -> Parser g s b
   Parser p <*> Parser q = Parser r where
      r :: forall x. s -> (b -> s -> x) -> (ParseFailure Pos s -> x) -> x
      r rest success failure = p rest (\f rest'-> q rest' (success . f) failure) failure
   {-# INLINABLE (<*>) #-}

instance FactorialMonoid s => Alternative (Parser g s) where
   empty = Parser (\rest _ failure-> failure $ ParseFailure (fromEnd $ Factorial.length rest) [] [])
   (<|>) = alt

-- | A named and unconstrained version of the '<|>' operator
alt :: forall g s a. Parser g s a -> Parser g s a -> Parser g s a
Parser p `alt` Parser q = Parser r where
   r :: forall x. s -> (a -> s -> x) -> (ParseFailure Pos s -> x) -> x
   r rest success failure = p rest success (\f1-> q rest success $ \f2 -> failure (f1 <> f2))
   
instance Factorial.FactorialMonoid s => Filterable (Parser g s) where
   mapMaybe :: forall a b. (a -> Maybe b) -> Parser g s a -> Parser g s b
   mapMaybe f (Parser p) = Parser q where
      q :: forall x. s -> (b -> s -> x) -> (ParseFailure Pos s -> x) -> x
      q rest success failure = p rest (maybe filterFailure success . f) failure
         where filterFailure _ = failure (expected (fromEnd $ Factorial.length rest) "filter")
   {-# INLINABLE mapMaybe #-}

#if MIN_VERSION_base(4,13,0)
instance Monad (Parser g s) where
#else
instance Factorial.FactorialMonoid s => Monad (Parser g s) where
#endif
   return = pure
   (>>=) :: forall a b. Parser g s a -> (a -> Parser g s b) -> Parser g s b
   Parser p >>= f = Parser r where
      r :: forall x. s -> (b -> s -> x) -> (ParseFailure Pos s -> x) -> x
      r rest success failure = p rest (\a rest'-> applyParser (f a) rest' success failure) failure

#if MIN_VERSION_base(4,13,0)
instance FactorialMonoid s => MonadFail (Parser g s) where
#endif
   fail msg = Parser (\rest _ failure-> failure $
                       ParseFailure (fromEnd $ Factorial.length rest) [StaticDescription msg] [])

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
      where q :: forall x. s -> (a -> s -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success (const $ failure
                                                       $ ParseFailure (fromEnd $ Factorial.length input) [] [])
   (<?>) :: forall a. Parser g s a -> String -> Parser g s a
   Parser p <?> msg  = Parser q
      where q :: forall x. s -> (a -> s -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success (failure . replaceFailure)
               where replaceFailure (ParseFailure pos msgs erroneous) =
                        ParseFailure pos (if pos == fromEnd (Factorial.length input) then [StaticDescription msg]
                                          else msgs) erroneous
   eof = Parser p
      where p rest success failure
               | Null.null rest = success () rest
               | otherwise = failure (ParseFailure (fromEnd $ Factorial.length rest)
                                                   [StaticDescription "end of input"] [])
   unexpected msg = Parser (\t _ failure ->
                             failure $ ParseFailure (fromEnd $ Factorial.length t) [] [StaticDescription msg])
   notFollowedBy (Parser p) = Parser q
      where q :: forall x. s -> (() -> s -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success' failure'
               where success' _ _ =
                        failure (ParseFailure (fromEnd $ Factorial.length input) [StaticDescription "notFollowedBy"] [])
                     failure' _ = success () input

instance FactorialMonoid s => CommittedParsing (Parser g s) where
   type CommittedResults (Parser g s) = ParseResults s
   commit :: forall a. Parser g s a -> Parser g s (ParseResults s a)
   commit (Parser p) = Parser q
      where q :: forall x. s -> (ParseResults s a -> s -> x) -> (ParseFailure Pos s -> x) -> x
            q input success _failure = p input (success . Right) failure'
               where failure' f = success (Left f) input
   admit :: forall a. Parser g s (ParseResults s a) -> Parser g s a
   admit (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success' failure
               where success' (Left f) _rest = failure f
                     success' (Right a) rest = success a rest

-- | Every PEG parser is deterministic all the time.
instance FactorialMonoid s => DeterministicParsing (Parser g s) where
   (<<|>) = alt
   takeSome = some
   takeMany = many
   skipAll = skipMany

instance FactorialMonoid s => LookAheadParsing (Parser g s) where
   lookAhead :: forall a. Parser g s a -> Parser g s a
   lookAhead (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success' failure'
               where success' a _ = success a input
                     failure' f = failure f

instance (Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p :: forall x. s -> (Char -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> success first suffix
                  _ -> failure (expected (fromEnd $ Factorial.length rest) "Char.satisfy")
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (LeftReductive s, FactorialMonoid s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   getInput = Parser p
      where p rest success _ = success rest rest
   anyToken = Parser p
      where p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) -> success first suffix
                  _ -> failure (expected (fromEnd $ Factorial.length rest) "anyToken")
   satisfy predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) | predicate first -> success first suffix
                  _ -> failure (expected (fromEnd $ Factorial.length rest) "satisfy")
   notSatisfy predicate = Parser p
      where p :: forall x. s -> (() -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, _)
                     | predicate first -> failure (expected (fromEnd $ Factorial.length rest) "notSatisfy")
                  _ -> success () rest
   scan :: forall state. state -> (state -> s -> Maybe state) -> Parser g s s
   scan s0 f = Parser (p s0)
      where p :: forall x. state -> s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p s rest success _ = success prefix suffix
               where (prefix, suffix, _) = Factorial.spanMaybe' s f rest
   take n = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success _
               | (prefix, suffix) <- Factorial.splitAt n rest, Factorial.length prefix == n = success prefix suffix
            p rest _ failure = failure (expected (fromEnd $ Factorial.length rest) $ "take" ++ show n)
   takeWhile predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success _ | (prefix, suffix) <- Factorial.span predicate rest = success prefix suffix
   takeWhile1 predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure
               | (prefix, suffix) <- Factorial.span predicate rest =
                    if Null.null prefix
                    then failure (expected (fromEnd $ Factorial.length rest) "takeWhile1")
                    else success prefix suffix
   string s = Parser p where
      p :: forall x. s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
      p s' success failure
         | Just suffix <- stripPrefix s s' = success s suffix
         | otherwise = failure (ParseFailure (fromEnd $ Factorial.length s') [LiteralDescription s] [])
   {-# INLINABLE string #-}

instance InputParsing (Parser g s)  => TraceableParsing (Parser g s) where
   traceInput :: forall a. (s -> String) -> Parser g s a -> Parser g s a
   traceInput description (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> x) -> (ParseFailure Pos s -> x) -> x
            q rest success failure = traceWith "Parsing " (p rest success' failure')
               where traceWith prefix = trace (prefix <> description rest)
                     failure' f = traceWith "Failed " (failure f)
                     success' r suffix = traceWith "Parsed " (success r suffix)

instance (Show s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyCharInput predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> success (Factorial.primePrefix rest) suffix
                  _ -> failure (expected (fromEnd $ Factorial.length rest) "satisfyChar")
   notSatisfyChar predicate = Parser p
      where p :: forall x. s -> (() -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Textual.characterPrefix rest
               of Just first | predicate first
                               -> failure (expected (fromEnd $ Factorial.length rest) "notSatisfyChar")
                  _ -> success () rest
   scanChars :: forall state. state -> (state -> Char -> Maybe state) -> Parser g s s
   scanChars s0 f = Parser (p s0)
      where p :: forall x. state -> s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p s rest success _ = success prefix suffix
               where (prefix, suffix, _) = Textual.spanMaybe_' s f rest
   takeCharsWhile predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success _ | (prefix, suffix) <- Textual.span_ False predicate rest = success prefix suffix
   takeCharsWhile1 predicate = Parser p
      where p :: forall x. s -> (s -> s -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure
               | Null.null prefix = failure (expected (fromEnd $ Factorial.length rest) "takeCharsWhile1")
               | otherwise = success prefix suffix
               where (prefix, suffix) = Textual.span_ False predicate rest

-- | Continuation-passing PEG parser
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Continued.'Parser' g s) -> s -> g ('ParseResults' s)
-- @
instance (LeftReductive s, FactorialMonoid s) => MultiParsing (Parser g s) where
   type ResultFunctor (Parser g s) = ParseResults s
   -- | Returns an input prefix parse paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . (\p-> applyParser p input (flip $ curry Right) (Left . fromFailure))) g
   parseComplete g input = Rank2.fmap (\p-> applyParser p input (const . Right) (Left . fromFailure))
                                      (Rank2.fmap (<* eof) g)

fromFailure :: (Eq s, FactorialMonoid s) => ParseFailure Pos s -> ParseFailure Pos s
fromFailure (ParseFailure pos positive negative) = ParseFailure pos (nub positive) (nub negative)
