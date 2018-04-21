{-# LANGUAGE TypeFamilies, UndecidableInstances #-}
-- | Backtracking parser for Parsing Expression Grammars, tracking the consumed input length
module Text.Grampa.PEG.Backtrack.Measured (Parser(..), Result(..), alt) where

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
import Text.Grampa.Class (Lexical(..), MonoidParsing(..), MultiParsing(..), ParseResults, ParseFailure(..))
import Text.Grampa.Internal (FailureInfo(..))

data Result (g :: (* -> *) -> *) s v = Parsed{parsedLength :: !Int,
                                              parsedResult :: !v,
                                              parsedSuffix :: !s}
                                     | NoParse FailureInfo

-- | Parser type for Parsing Expression Grammars that uses a backtracking algorithm, fast for grammars in LL(1) class
-- but with potentially exponential performance for longer ambiguous prefixes.
newtype Parser g s r = Parser{applyParser :: s -> Result g s r}

instance Show1 (Result g s) where
   liftShowsPrec showsPrecSub _showList prec Parsed{parsedResult= r} rest = "Parsed " ++ showsPrecSub prec r rest
   liftShowsPrec _showsPrec _showList _prec (NoParse f) rest = "NoParse " ++ shows f rest

instance Functor (Result g s) where
   fmap f (Parsed l a rest) = Parsed l (f a) rest
   fmap _ (NoParse failure) = NoParse failure
   
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

instance Factorial.FactorialMonoid s => Alternative (Parser g s) where
   empty = Parser (\rest-> NoParse $ FailureInfo 0 (fromIntegral $ Factorial.length rest) ["empty"])
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
               of Parsed l a rest' -> case applyParser (f a) rest'
                                      of Parsed l' b rest'' -> Parsed (l+l') b rest''
                                         NoParse failure -> NoParse failure
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
   try (Parser p) = Parser (weakenFailure . p)
      where weakenFailure (NoParse (FailureInfo s pos msgs)) = NoParse (FailureInfo (pred s) pos msgs)
            weakenFailure r = r
   Parser p <?> msg  = Parser q
      where q rest = strengthenFailure rest (p rest)
            strengthenFailure rest (NoParse (FailureInfo s _pos _msgs)) =
               NoParse (FailureInfo (succ s) (fromIntegral $ Factorial.length rest) [msg])
            strengthenFailure _ r = r
   eof = endOfInput
   unexpected msg = Parser (\t-> NoParse $ FailureInfo 0 (fromIntegral $ Factorial.length t) [msg])
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t Parsed{} = NoParse (FailureInfo 1 (fromIntegral $ Factorial.length t) ["notFollowedBy"])
            rewind t NoParse{} = Parsed 0 () t

instance Factorial.FactorialMonoid s => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (Parsed _ r _) = Parsed 0 r t
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

instance MonoidParsing (Parser g) where
   endOfInput = Parser p
      where p rest
               | Null.null rest = Parsed 0 () rest
               | otherwise = NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["endOfInput"])
   getInput = Parser p
      where p rest = Parsed (Factorial.length rest) rest mempty
   anyToken = Parser p
      where p rest = case Factorial.splitPrimePrefix rest
                     of Just (first, suffix) -> Parsed 1 first suffix
                        _ -> NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["anyToken"])
   satisfy predicate = Parser p
      where p rest =
               case Factorial.splitPrimePrefix rest
               of Just (first, suffix) | predicate first -> Parsed 1 first suffix
                  _ -> NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["satisfy"])
   satisfyChar predicate = Parser p
      where p rest =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> Parsed 1 first suffix
                  _ -> NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["satisfyChar"])
   satisfyCharInput predicate = Parser p
      where p rest =
               case Textual.splitCharacterPrefix rest
               of Just (first, suffix) | predicate first -> Parsed 1 (Factorial.primePrefix rest) suffix
                  _ -> NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["satisfyChar"])
   notSatisfy predicate = Parser p
      where p s = case Factorial.splitPrimePrefix s
                  of Just (first, _) 
                        | predicate first -> NoParse (FailureInfo 1 (fromIntegral $ Factorial.length s) ["notSatisfy"])
                     _ -> Parsed 0 () s
   notSatisfyChar predicate = Parser p
      where p s = case Textual.characterPrefix s
                  of Just first | predicate first 
                                  -> NoParse (FailureInfo 1 (fromIntegral $ Factorial.length s) ["notSatisfyChar"])
                     _ -> Parsed 0 () s
   scan s0 f = Parser (p s0)
      where p s rest = Parsed (Factorial.length prefix) prefix suffix
               where (prefix, suffix, _) = Factorial.spanMaybe' s f rest
   scanChars s0 f = Parser (p s0)
      where p s rest = Parsed (Factorial.length prefix) prefix suffix
               where (prefix, suffix, _) = Textual.spanMaybe_' s f rest
   takeWhile predicate = Parser p
      where p rest | (prefix, suffix) <- Factorial.span predicate rest =
               Parsed (Factorial.length prefix) prefix suffix
   takeWhile1 predicate = Parser p
      where p rest | (prefix, suffix) <- Factorial.span predicate rest =
                        if Null.null prefix
                        then NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["takeWhile1"])
                        else Parsed (Factorial.length prefix) prefix suffix
   takeCharsWhile predicate = Parser p
      where p rest | (prefix, suffix) <- Textual.span_ False predicate rest = 
               Parsed (Factorial.length prefix) prefix suffix
   takeCharsWhile1 predicate = Parser p
      where p rest | (prefix, suffix) <- Textual.span_ False predicate rest =
                     if Null.null prefix
                     then NoParse (FailureInfo 1 (fromIntegral $ Factorial.length rest) ["takeCharsWhile1"])
                     else Parsed (Factorial.length prefix) prefix suffix
   string s = Parser p where
      p s' | Just suffix <- Cancellative.stripPrefix s s' = Parsed l s suffix
           | otherwise = NoParse (FailureInfo 1 (fromIntegral $ Factorial.length s') ["string " ++ show s])
      l = Factorial.length s
   concatMany (Parser p) = Parser q
      where q rest = case p rest
                     of Parsed l prefix suffix -> let Parsed l' prefix' suffix' = q suffix
                                                  in Parsed (l+l') (mappend prefix prefix') suffix'
                        NoParse{} -> Parsed 0 mempty rest
   {-# INLINABLE string #-}

-- | Backtracking PEG parser
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Backtrack.'Parser' g s) -> s -> g 'ParseResults'
-- @
instance MultiParsing Parser where
   type ResultFunctor Parser = ParseResults
   {-# NOINLINE parsePrefix #-}
   -- | Returns an input prefix parse paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . fromResult input . (`applyParser` input)) g
   parseComplete g input = Rank2.fmap ((snd <$>) . fromResult input . (`applyParser` input))
                                      (Rank2.fmap (<* endOfInput) g)

fromResult :: FactorialMonoid s => s -> Result g s r -> ParseResults (s, r)
fromResult s (NoParse (FailureInfo _ pos msgs)) =
   Left (ParseFailure (Factorial.length s - fromIntegral pos + 1) (nub msgs))
fromResult _ (Parsed _ prefix suffix) = Right (suffix, prefix)
