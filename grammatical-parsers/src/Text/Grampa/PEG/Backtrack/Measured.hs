{-# LANGUAGE CPP, FlexibleContexts, TypeFamilies, UndecidableInstances #-}
-- | Backtracking parser for Parsing Expression Grammars, tracking the consumed input length
module Text.Grampa.PEG.Backtrack.Measured (Parser(..), Result(..), alt) where

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
                          InputParsing(..), InputCharParsing(..), ConsumedInputParsing(..),
                          MultiParsing(..), ParseResults, ParseFailure(..), FailureDescription(..), Pos)
import Text.Grampa.Internal (expected, TraceableParsing(..))

data Result (g :: (* -> *) -> *) s v = Parsed{parsedLength :: !Int,
                                              parsedResult :: !v,
                                              parsedSuffix :: !s}
                                     | NoParse (ParseFailure Pos s)

-- | Parser type for Parsing Expression Grammars that uses a backtracking algorithm, fast for grammars in LL(1) class
-- but with potentially exponential performance for longer ambiguous prefixes.
newtype Parser g s r = Parser{applyParser :: s -> Result g s r}

instance Show s => Show1 (Result g s) where
   liftShowsPrec showsPrecSub _showList prec Parsed{parsedResult= r} rest = "Parsed " ++ showsPrecSub prec r rest
   liftShowsPrec _showsPrec _showList _prec (NoParse f) rest = "NoParse " ++ shows f rest

instance Functor (Result g s) where
   fmap f (Parsed l a rest) = Parsed l (f a) rest
   fmap _ (NoParse failure) = NoParse failure

instance Factorial.FactorialMonoid s => Filterable (Result g s) where
   mapMaybe f (Parsed l a rest) =
      maybe (NoParse $ expected (fromEnd $ Factorial.length rest) "filter") (\b-> Parsed l b rest) (f a)
   mapMaybe _ (NoParse failure) = NoParse failure
   
instance Functor (Parser g s) where
   fmap f (Parser p) = Parser (fmap f . p)
   {-# INLINABLE fmap #-}

instance Applicative (Parser g s) where
   pure a = Parser (Parsed 0 a)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of Parsed l f rest' -> case q rest'
                                      of Parsed l' a rest'' -> Parsed (l+l') (f a) rest''
                                         NoParse failure -> NoParse failure
                  NoParse failure -> NoParse failure
   {-# INLINABLE (<*>) #-}

instance FactorialMonoid s => Alternative (Parser g s) where
   empty = Parser (\rest-> NoParse $ ParseFailure (fromEnd $ Factorial.length rest) [] [])
   (<|>) = alt

-- | A named and unconstrained version of the '<|>' operator
alt :: Parser g s a -> Parser g s a -> Parser g s a
Parser p `alt` Parser q = Parser r where
      r rest = case p rest
               of x@Parsed{} -> x
                  NoParse{} -> q rest
   
instance FactorialMonoid s => Filterable (Parser g s) where
   mapMaybe f (Parser p) = Parser (mapMaybe f . p)
   {-# INLINABLE mapMaybe #-}

#if MIN_VERSION_base(4,13,0)
instance Monad (Parser g s) where
#else
instance Factorial.FactorialMonoid s => Monad (Parser g s) where
#endif
   return = pure
   Parser p >>= f = Parser r where
      r rest = case p rest
               of Parsed l a rest' -> case applyParser (f a) rest'
                                      of Parsed l' b rest'' -> Parsed (l+l') b rest''
                                         NoParse failure -> NoParse failure
                  NoParse failure -> NoParse failure

#if MIN_VERSION_base(4,13,0)
instance FactorialMonoid s => MonadFail (Parser g s) where
#endif
   fail msg = Parser (\rest-> NoParse $ ParseFailure (fromEnd $ Factorial.length rest) [] [StaticDescription msg])

instance FactorialMonoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Semigroup x => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = (<>)

instance FactorialMonoid s => Parsing (Parser g s) where
   try (Parser p) = Parser q
      where q rest = rewindFailure (p rest)
               where rewindFailure NoParse{} = NoParse (ParseFailure (fromEnd $ Factorial.length rest) [] [])
                     rewindFailure parsed = parsed
   Parser p <?> msg  = Parser q
      where q rest = replaceFailure (p rest)
               where replaceFailure (NoParse (ParseFailure pos msgs erroneous)) =
                        NoParse (ParseFailure pos
                                    (if pos == fromEnd (Factorial.length rest) then [StaticDescription msg] else msgs)
                                    erroneous)
                     replaceFailure parsed = parsed
   eof = Parser p
      where p rest
               | Null.null rest = Parsed 0 () rest
               | otherwise = NoParse (ParseFailure (fromEnd $ Factorial.length rest)
                                                   [StaticDescription "end of input"] [])
   unexpected msg = Parser (\t-> NoParse $ ParseFailure (fromEnd $ Factorial.length t) [] [StaticDescription msg])
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t Parsed{} = NoParse (ParseFailure (fromEnd $ Factorial.length t)
                                                      [StaticDescription "notFollowedBy"] [])
            rewind t NoParse{} = Parsed 0 () t

instance FactorialMonoid s => CommittedParsing (Parser g s) where
   type CommittedResults (Parser g s) = ParseResults s
   commit (Parser p) = Parser q
      where q rest = case p rest
                     of NoParse failure -> Parsed 0 (Left failure) rest
                        Parsed len a rest' -> Parsed len (Right a) rest'
   admit (Parser p) = Parser q
      where q rest = case p rest
                     of NoParse failure -> NoParse failure
                        Parsed _ (Left failure) _ -> NoParse failure
                        Parsed len (Right a) rest' -> Parsed len a rest'

-- | Every PEG parser is deterministic all the time.
instance FactorialMonoid s => DeterministicParsing (Parser g s) where
   (<<|>) = alt
   takeSome = some
   takeMany = many
   skipAll = skipMany

instance FactorialMonoid s => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (Parsed _ r _) = Parsed 0 r t
            rewind _ r@NoParse{} = r

instance (Show s, Textual.TextualMonoid s) => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p rest =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> Parsed 1 first suffix
                  _ -> NoParse (expected (fromEnd $ Factorial.length rest) "Char.satisfy")
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Cancellative.LeftReductive s, FactorialMonoid s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   getInput = Parser p
      where p rest = Parsed 0 rest rest
   anyToken = Parser p
      where p rest = case Factorial.splitPrimePrefix rest
                     of Just (first, suffix) -> Parsed 1 first suffix
                        _ -> NoParse (expected (fromEnd $ Factorial.length rest) "anyToken")
   satisfy predicate = Parser p
      where p rest =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) | predicate first -> Parsed 1 first suffix
                  _ -> NoParse (expected (fromEnd $ Factorial.length rest) "satisfy")
   notSatisfy predicate = Parser p
      where p s = case Factorial.splitPrimePrefix s
                  of Just (first, _) 
                        | predicate first -> NoParse (expected (fromEnd $ Factorial.length s) "notSatisfy")
                     _ -> Parsed 0 () s
   scan s0 f = Parser (p s0)
      where p s rest = Parsed (Factorial.length prefix) prefix suffix
               where (prefix, suffix, _) = Factorial.spanMaybe' s f rest
   take n = Parser p
      where p rest
              | (prefix, suffix) <- Factorial.splitAt n rest, Factorial.length prefix == n = Parsed n prefix suffix
              | otherwise = NoParse (expected (fromEnd $ Factorial.length rest) $ "take " ++ show n)
   takeWhile predicate = Parser p
      where p rest | (prefix, suffix) <- Factorial.span predicate rest =
               Parsed (Factorial.length prefix) prefix suffix
   takeWhile1 predicate = Parser p
      where p rest | (prefix, suffix) <- Factorial.span predicate rest =
                        if Null.null prefix
                        then NoParse (expected (fromEnd $ Factorial.length rest) "takeWhile1")
                        else Parsed (Factorial.length prefix) prefix suffix
   string s = Parser p where
      p s' | Just suffix <- Cancellative.stripPrefix s s' = Parsed l s suffix
           | otherwise = NoParse (ParseFailure (fromEnd $ Factorial.length s') [LiteralDescription s] [])
      l = Factorial.length s
   {-# INLINABLE string #-}

instance (Cancellative.LeftReductive s, FactorialMonoid s) => ConsumedInputParsing (Parser g s) where
   match (Parser p) = Parser q
      where q rest = case p rest
                     of Parsed l prefix suffix -> Parsed l (Factorial.take l rest, prefix) suffix
                        NoParse failure -> NoParse failure

instance InputParsing (Parser g s)  => TraceableParsing (Parser g s) where
   traceInput description (Parser p) = Parser q
      where q s = case traceWith "Parsing " (p s)
                  of r@Parsed{} -> traceWith "Parsed " r
                     r@NoParse{} -> traceWith "Failed " r
               where traceWith prefix = trace (prefix <> description s)

instance (Show s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyCharInput predicate = Parser p
      where p rest =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> Parsed 1 (Factorial.primePrefix rest) suffix
                  _ -> NoParse (expected (fromEnd $ Factorial.length rest) "satisfyChar")
   notSatisfyChar predicate = Parser p
      where p s = case Textual.characterPrefix s
                  of Just first | predicate first 
                                  -> NoParse (expected (fromEnd $ Factorial.length s) "notSatisfyChar")
                     _ -> Parsed 0 () s
   scanChars s0 f = Parser (p s0)
      where p s rest = Parsed (Factorial.length prefix) prefix suffix
               where (prefix, suffix, _) = Textual.spanMaybe_' s f rest
   takeCharsWhile predicate = Parser p
      where p rest | (prefix, suffix) <- Textual.span_ False predicate rest = 
               Parsed (Factorial.length prefix) prefix suffix
   takeCharsWhile1 predicate = Parser p
      where p rest | (prefix, suffix) <- Textual.span_ False predicate rest =
                     if Null.null prefix
                     then NoParse (expected (fromEnd $ Factorial.length rest) "takeCharsWhile1")
                     else Parsed (Factorial.length prefix) prefix suffix

-- | Backtracking PEG parser
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Backtrack.'Parser' g s) -> s -> g ('ParseResults' s)
-- @
instance (Cancellative.LeftReductive s, Factorial.FactorialMonoid s) => MultiParsing (Parser g s) where
   type ResultFunctor (Parser g s) = ParseResults s
   {-# NOINLINE parsePrefix #-}
   -- | Returns an input prefix parse paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . fromResult . (`applyParser` input)) g
   parseComplete g input = Rank2.fmap ((snd <$>) . fromResult . (`applyParser` input))
                                      (Rank2.fmap (<* eof) g)

fromResult :: (Eq s, FactorialMonoid s) => Result g s r -> ParseResults s (s, r)
fromResult (NoParse failure) = Left failure
fromResult (Parsed _ prefix suffix) = Right (suffix, prefix)
