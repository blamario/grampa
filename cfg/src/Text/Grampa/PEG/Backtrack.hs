{-# LANGUAGE TypeFamilies #-}
-- | Backtracking parser
module Text.Grampa.PEG.Backtrack (Parser, parse) where

import Control.Applicative (Applicative(..), Alternative(..), liftA2)
import Control.Monad (Monad(..), MonadPlus(..))

import Data.Char (isSpace)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (nub)
import Data.Monoid (Monoid(mappend, mempty), (<>))
import Data.Monoid.Factorial(FactorialMonoid)
import Data.Word (Word64)

import qualified Data.Monoid.Cancellative as Cancellative
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Null as Null
import qualified Data.Monoid.Textual as Textual

import qualified Rank2

import Text.Parser.Combinators (Parsing(..))
import Text.Grampa.Class (MonoidParsing(..), ParseResults, ParseFailure(..))

data Result (g :: (* -> *) -> *) s v = Parsed{parsedPrefix :: v, 
                                              parsedSuffix :: s}
                                     | NoParse FailureInfo
data FailureInfo = FailureInfo !Int Word64 [String] deriving (Eq, Show)

-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
newtype Parser g s r = Parser{applyParser :: s -> Result g s r}

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

instance Factorial.FactorialMonoid s => Alternative (Parser g s) where
   empty = Parser (\rest-> NoParse $ FailureInfo 0 (fromIntegral $ Factorial.length rest) ["empty"])
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

instance Factorial.FactorialMonoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance Factorial.FactorialMonoid s => Parsing (Parser g s) where
   try = id
   (<?>) = const
   eof = endOfInput
   unexpected msg = Parser (\t-> NoParse $ FailureInfo 0 (fromIntegral $ Factorial.length t) [msg])
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t Parsed{} = NoParse (FailureInfo 1 (fromIntegral $ Factorial.length t) ["notFollowedBy"])
            rewind t NoParse{} = Parsed () t

instance MonoidParsing (Parser g) where
   Parser p <<|> Parser q = Parser r where
      r rest = case p rest
               of x@Parsed{} -> x
                  NoParse{} -> q rest
   endOfInput = Parser p
      where p rest = if Null.null rest
                     then NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["endOfInput"])
                     else Parsed () rest
   getInput = Parser p
      where p rest = Parsed rest mempty
   anyToken = Parser p
      where p rest = case Factorial.splitPrimePrefix rest
                     of Just (first, suffix) -> Parsed first suffix
                        _ -> NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["anyToken"])
   satisfy predicate = Parser p
      where p rest =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) | predicate first -> Parsed first suffix
                  _ -> NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["satisfy"])
   satisfyChar predicate = Parser p
      where p rest =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> Parsed first suffix
                  _ -> NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["satisfyChar"])
   scan s0 f = Parser (p s0)
      where p s rest = Parsed prefix suffix
               where (prefix, suffix, _) = Factorial.spanMaybe' s f rest
   scanChars s0 f = Parser (p s0)
      where p s rest = Parsed prefix suffix
               where (prefix, suffix, _) = Textual.spanMaybe_' s f rest
   takeWhile predicate = Parser p
      where p rest | (prefix, suffix) <- Factorial.span predicate rest = Parsed prefix suffix
   takeWhile1 predicate = Parser p
      where p rest | (prefix, suffix) <- Factorial.span predicate rest =
                        if Null.null prefix
                        then NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["takeWhile1"])
                        else Parsed prefix suffix
   takeCharsWhile predicate = Parser p
      where p rest | (prefix, suffix) <- Textual.span_ False predicate rest = Parsed prefix suffix
   takeCharsWhile1 predicate = Parser p
      where p rest | (prefix, suffix) <- Textual.span_ False predicate rest =
                     if Null.null prefix
                     then NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["takeCharsWhile1"])
                     else Parsed prefix suffix
   string s = Parser p where
      p s' | Just suffix <- Cancellative.stripPrefix s s' = Parsed s suffix
           | otherwise = NoParse (FailureInfo 1 (fromIntegral $ Factorial.length s') ["string " ++ show s])
   whiteSpace = () <$ takeCharsWhile isSpace
   concatMany (Parser p) = Parser q
      where q rest = case p rest
                     of Parsed prefix suffix -> let Parsed prefix' suffix' = q suffix
                                                in Parsed (prefix <> prefix') suffix'
                        NoParse{} -> Parsed mempty rest


{-# NOINLINE parse #-}
parse :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> g (Compose ParseResults ((,) s))
--parse :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> [(s, g (Result g s))]
parse g input = Rank2.fmap (Compose . fromResult input . (`applyParser` input)) g

fromResult :: FactorialMonoid s => s -> Result g s r -> ParseResults (s, r)
fromResult s (NoParse (FailureInfo _ pos msgs)) =
   Left (ParseFailure (Factorial.length s - fromIntegral pos + 1) (nub msgs))
fromResult _ (Parsed prefix suffix) = Right (suffix, prefix)
