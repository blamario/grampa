{-# LANGUAGE CPP, FlexibleContexts, InstanceSigs, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
-- | Continuation-passing parser for context-free grammars
module Text.Grampa.ContextFree.Continued (Parser(..), Result(..), alt) where

import Control.Applicative (Applicative(..), Alternative(..), liftA2)
import Control.Monad (Monad(..), MonadPlus(..))
#if MIN_VERSION_base(4,13,0)
import Control.Monad (MonadFail(fail))
#endif

import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.Semigroup (Semigroup(..))
import Data.Monoid (Monoid(mappend, mempty))
import Data.Monoid.Factorial(FactorialMonoid)
import Data.Monoid.Textual(TextualMonoid)
import Data.String (fromString)
import Debug.Trace (trace)
import Witherable (Filterable(mapMaybe))

import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Null as Null
import qualified Data.Monoid.Textual as Textual
import qualified Data.Semigroup.Cancellative as Cancellative

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

-- | Parser type for context-free grammars that uses a continuation-passing algorithm, fast for grammars in LL(1)
-- class but with potentially exponential performance for longer ambiguous prefixes.
newtype Parser (g :: (* -> *) -> *) s r =
   Parser{applyParser :: forall x. s -> (r -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x}

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
   pure a = Parser (\input success failure-> success a input failure)
   (<*>) :: forall a b. Parser g s (a -> b) -> Parser g s a -> Parser g s b
   Parser p <*> Parser q = Parser r where
      r :: forall x. s -> (b -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
      r rest success failure = p rest (\f rest'-> q rest' (success . f)) failure
   {-# INLINABLE (<*>) #-}

instance (Factorial.FactorialMonoid s, Ord s) => Alternative (Parser g s) where
   empty = Parser (\rest _ failure-> failure $ ParseFailure (fromEnd $ Factorial.length rest) [] [])
   (<|>) = alt

-- | A named and unconstrained version of the '<|>' operator
alt :: forall g s a. Ord s => Parser g s a -> Parser g s a -> Parser g s a
Parser p `alt` Parser q = Parser r where
   r :: forall x. s -> (a -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
   r rest success failure = p rest success' failure'
      where success' a rest' _ = success a rest' failure'
            failure' f1 = q rest success (\f2 -> failure (f1 <> f2))

instance Factorial.FactorialMonoid s => Filterable (Result g s) where
   mapMaybe f (Parsed a rest) =
      maybe (NoParse $ expected (fromEnd $ Factorial.length rest) "filter") (`Parsed` rest) (f a)
   mapMaybe _ (NoParse failure) = NoParse failure
   
instance Factorial.FactorialMonoid s => Filterable (Parser g s) where
   mapMaybe :: forall a b. (a -> Maybe b) -> Parser g s a -> Parser g s b
   mapMaybe f (Parser p) = Parser q where
      q :: forall x. s -> (b -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
      q rest success failure = p rest (maybe filterFailure success . f) failure
         where filterFailure _ _ = failure (expected (fromEnd $ Factorial.length rest) "filter")
   {-# INLINABLE mapMaybe #-}

#if MIN_VERSION_base(4,13,0)
instance Monad (Parser g s) where
#else
instance Factorial.FactorialMonoid s => Monad (Parser g s) where
#endif
   return = pure
   (>>=) :: forall a b. Parser g s a -> (a -> Parser g s b) -> Parser g s b
   Parser p >>= f = Parser r where
      r :: forall x. s -> (b -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
      r rest success failure = p rest (\a rest'-> applyParser (f a) rest' success) failure

#if MIN_VERSION_base(4,13,0)
instance Factorial.FactorialMonoid s => MonadFail (Parser g s) where
#endif
   fail msg = Parser (\rest _ failure->
                       failure $ ParseFailure (fromEnd $ Factorial.length rest) [] [StaticDescription msg])

instance (Factorial.FactorialMonoid s, Ord s) => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Semigroup x => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = (<>)

instance (Factorial.FactorialMonoid s, Ord s) => Parsing (Parser g s) where
   try :: forall a. Parser g s a -> Parser g s a
   try (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success (failure . rewindFailure)
               where rewindFailure ParseFailure{} = ParseFailure (fromEnd $ Factorial.length input) [] []
   (<?>) :: forall a. Parser g s a -> String -> Parser g s a
   Parser p <?> msg  = Parser q
      where q :: forall x. s -> (a -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success (failure . replaceFailure)
               where replaceFailure (ParseFailure pos msgs erroneous) =
                        ParseFailure pos (if pos == fromEnd (Factorial.length input) then [StaticDescription msg]
                                          else msgs) erroneous

   eof = Parser p
      where p rest success failure
               | Null.null rest = success () rest failure
               | otherwise = failure (expected (fromEnd $ Factorial.length rest) "end of input")
   unexpected msg = Parser (\t _ failure ->
                             failure $ ParseFailure (fromEnd $ Factorial.length t) [] [StaticDescription msg])
   notFollowedBy (Parser p) = Parser q
      where q :: forall x. s -> (() -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success' failure'
               where success' _ _ _ = failure (expected (fromEnd $ Factorial.length input) "notFollowedBy")
                     failure' _ = success () input failure

instance (FactorialMonoid s, Ord s) => DeterministicParsing (Parser g s) where
   (<<|>) :: forall a. Parser g s a -> Parser g s a -> Parser g s a
   Parser p <<|> Parser q = Parser r where
      r :: forall x. s -> (a -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
      r rest success failure = p rest success' failure'
         where success' a rest' _ = success a rest' failure
               failure' f1 = q rest success (\f2 -> failure (f1 <> f2))
   takeSome p = (:) <$> p <*> takeMany p
   takeMany p = takeSome p <<|> pure []

instance (FactorialMonoid s, Ord s) => CommittedParsing (Parser g s) where
   type CommittedResults (Parser g s) = ParseResults s
   commit :: forall a. Parser g s a -> Parser g s (ParseResults s a)
   commit (Parser p) = Parser q
      where q :: forall x. s -> (ParseResults s a -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input (success . Right) failure'
               where failure' f = success (Left f) input failure
   admit :: forall a. Parser g s (ParseResults s a) -> Parser g s a
   admit (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success' failure
               where success' (Left f) _rest = const (failure f)
                     success' (Right a) rest = success a rest

instance (FactorialMonoid s, Ord s) => LookAheadParsing (Parser g s) where
   lookAhead :: forall a. Parser g s a -> Parser g s a
   lookAhead (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            q input success failure = p input success' failure'
               where success' a _ = success a input
                     failure' f = failure f

instance (Ord s, Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p :: forall x. s -> (Char -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> success first suffix failure
                  _ -> failure (expected (fromEnd $ Factorial.length rest) "Char.satisfy")
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Cancellative.LeftReductive s, Factorial.FactorialMonoid s, Ord s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   getInput = Parser p
      where p rest success failure = success rest rest failure
   anyToken = Parser p
      where p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) -> success first suffix failure
                  _ -> failure (expected (fromEnd $ Factorial.length rest) "anyToken")
   satisfy predicate = Parser p
      where p :: forall x. s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) | predicate first -> success first suffix failure
                  _ -> failure (expected (fromEnd $ Factorial.length rest) "satisfy")
   notSatisfy predicate = Parser p
      where p :: forall x. s -> (() -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Factorial.splitPrimePrefix rest
               of Just (first, _)
                     | predicate first -> failure (expected (fromEnd $ Factorial.length rest) "notSatisfy")
                  _ -> success () rest failure
   scan :: forall state. state -> (state -> s -> Maybe state) -> Parser g s s
   scan s0 f = Parser (p s0)
      where p :: forall x. state -> s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p s rest success failure = success prefix suffix failure
               where (prefix, suffix, _) = Factorial.spanMaybe' s f rest
   take n = Parser p
      where p :: forall x. s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure
              | (prefix, suffix) <- Factorial.splitAt n rest,
                Factorial.length prefix == n = success prefix suffix failure
              | otherwise = failure (expected (fromEnd $ Factorial.length rest) $ "take " ++ show n)
   takeWhile predicate = Parser p
      where p :: forall x. s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure | (prefix, suffix) <- Factorial.span predicate rest = success prefix suffix failure
   takeWhile1 predicate = Parser p
      where p :: forall x. s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure
               | (prefix, suffix) <- Factorial.span predicate rest =
                    if Null.null prefix
                    then failure (expected (fromEnd $ Factorial.length rest) "takeWhile1")
                    else success prefix suffix failure
   string s = Parser p where
      p :: forall x. s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
      p s' success failure
         | Just suffix <- Cancellative.stripPrefix s s' = success s suffix failure
         | otherwise = failure (ParseFailure (fromEnd $ Factorial.length s') [LiteralDescription s] [])
   {-# INLINABLE string #-}

instance InputParsing (Parser g s)  => TraceableParsing (Parser g s) where
   traceInput :: forall a. (s -> String) -> Parser g s a -> Parser g s a
   traceInput description (Parser p) = Parser q
      where q :: forall x. s -> (a -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            q rest success failure = traceWith "Parsing " (p rest success' failure')
               where traceWith prefix = trace (prefix <> description rest)
                     failure' f = traceWith "Failed " (failure f)
                     success' r suffix failure'' = traceWith "Parsed " (success r suffix failure'')

instance (Ord s, Show s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyCharInput predicate = Parser p
      where p :: forall x. s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> success (Factorial.primePrefix rest) suffix failure
                  _ -> failure (expected (fromEnd $ Factorial.length rest) "satisfyChar")
   notSatisfyChar predicate = Parser p
      where p :: forall x. s -> (() -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure =
               case Textual.characterPrefix rest
               of Just first | predicate first
                               -> failure (expected (fromEnd $ Factorial.length rest) "notSatisfyChar")
                  _ -> success () rest failure
   scanChars :: forall state. state -> (state -> Char -> Maybe state) -> Parser g s s
   scanChars s0 f = Parser (p s0)
      where p :: forall x. state -> s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p s rest success failure = success prefix suffix failure
               where (prefix, suffix, _) = Textual.spanMaybe_' s f rest
   takeCharsWhile predicate = Parser p
      where p :: forall x. s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure
               | (prefix, suffix) <- Textual.span_ False predicate rest = success prefix suffix failure
   takeCharsWhile1 predicate = Parser p
      where p :: forall x. s -> (s -> s -> (ParseFailure Pos s -> x) -> x) -> (ParseFailure Pos s -> x) -> x
            p rest success failure
               | Null.null prefix = failure (expected (fromEnd $ Factorial.length rest) "takeCharsWhile1")
               | otherwise = success prefix suffix failure
               where (prefix, suffix) = Textual.span_ False predicate rest

-- | Continuation-passing context-free parser
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Continued.'Parser' g s) -> s -> g ('ParseResults' s)
-- @
instance (Cancellative.LeftReductive s, Factorial.FactorialMonoid s, Ord s) => MultiParsing (Parser g s) where
   type ResultFunctor (Parser g s) = ParseResults s
   -- | Returns an input prefix parse paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . (\p-> applyParser p input (\a rest _-> Right (rest, a)) Left)) g
   parseComplete g input = Rank2.fmap (\p-> applyParser p input (const . const . Right) Left)
                                      (Rank2.fmap (<* eof) g)
