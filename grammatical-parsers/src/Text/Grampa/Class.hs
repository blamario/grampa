{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DefaultSignatures, DeriveDataTypeable, DeriveFunctor,
             FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, OverloadedStrings,
             RankNTypes, ScopedTypeVariables, TypeApplications, TypeFamilies, TypeSynonymInstances,
             UndecidableInstances #-}
module Text.Grampa.Class (MultiParsing(..), GrammarParsing(..),
                          AmbiguousParsing(..), DeterministicParsing(..), InputParsing(..), InputCharParsing(..),
                          ConsumedInputParsing(..), LexicalParsing(..), TailsParsing(..),
                          ParseResults, ParseFailure(..), Expected(..), Pos,
                          Ambiguous(..), completeParser) where

import Control.Applicative (Alternative(empty), liftA2)
import Data.Char (isAlphaNum, isLetter, isSpace)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Data (Data)
import Data.Typeable (Typeable)
import Data.Monoid (Monoid(mempty, mappend))
import qualified Data.Monoid.Null as Null
import Data.Monoid.Null (MonoidNull)
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)
import Data.Semigroup (Semigroup((<>)))
import Data.Ord (Down)
import Text.Parser.Combinators (Parsing((<?>)))
import Text.Parser.Token (TokenParsing)
import Text.Parser.Deterministic (DeterministicParsing(..))
import Text.Parser.Input (ConsumedInputParsing(..), InputParsing(..), InputCharParsing(..))
import Text.Parser.Input.Position (Position)
import qualified Text.Parser.Char
import Data.Kind (Constraint)

import qualified Rank2

import Prelude hiding (takeWhile)

type ParseResults s = Either (ParseFailure Pos s)

-- | A 'ParseFailure' contains the offset of the parse failure and the list of things expected at that offset.
data ParseFailure pos s = ParseFailure pos [Expected s] deriving (Eq, Functor, Show)

data Expected s = Expected String -- ^ a readable description of the expected input
                | ExpectedInput s -- ^ a literal piece of expected input
                deriving (Functor, Eq, Ord, Read, Show)

-- | Opaque type representing a position in the input.
newtype Pos = Pos (Down Int) deriving (Eq, Ord, Num, Position, Show)

-- | An 'Ambiguous' parse result, produced by the 'ambiguous' combinator, contains a 'NonEmpty' list of
-- alternative results.
newtype Ambiguous a = Ambiguous{getAmbiguous :: NonEmpty a} deriving (Data, Eq, Ord, Show, Typeable)

instance Show1 Ambiguous where
   liftShowsPrec sp sl d (Ambiguous (h :| l)) t
      | d > 5 = "(Ambiguous $ " <> sp 0 h (" :| " <> sl l (')' : t))
      | otherwise = "Ambiguous (" <> sp 0 h (" :| " <> sl l (')' : t))

instance Functor Ambiguous where
   fmap f (Ambiguous a) = Ambiguous (fmap f a)

instance Applicative Ambiguous where
   pure a = Ambiguous (pure a)
   Ambiguous f <*> Ambiguous a = Ambiguous (f <*> a)

instance Monad Ambiguous where
   return = pure
   Ambiguous a >>= f = Ambiguous (a >>= getAmbiguous . f)

instance Foldable Ambiguous where
   foldMap f (Ambiguous a) = foldMap f a

instance Traversable Ambiguous where
   traverse f (Ambiguous a) = Ambiguous <$> traverse f a

instance Semigroup a => Semigroup (Ambiguous a) where
   Ambiguous xs <> Ambiguous ys = Ambiguous (liftA2 (<>) xs ys)

instance Monoid a => Monoid (Ambiguous a) where
   mempty = Ambiguous (mempty :| [])
   Ambiguous xs `mappend` Ambiguous ys = Ambiguous (liftA2 mappend xs ys)

completeParser :: MonoidNull s => Compose (ParseResults s) (Compose [] ((,) s)) r -> Compose (ParseResults s) [] r
completeParser (Compose (Left failure)) = Compose (Left failure)
completeParser (Compose (Right (Compose results))) =
   case filter (Null.null . fst) results
   of [] -> Compose (Left $ ParseFailure 0 [Expected "complete parse"])
      completeResults -> Compose (Right $ snd <$> completeResults)

-- | Choose one of the instances of this class to parse with.
class InputParsing m => MultiParsing m where
   -- | Some parser types produce a single result, others a list of results.
   type ResultFunctor m :: * -> *
   type GrammarConstraint m (g :: (* -> *) -> *) :: Constraint
   type GrammarConstraint m g = Rank2.Functor g
   -- | Given a rank-2 record of parsers and input, produce a record of parses of the complete input.
   parseComplete :: (ParserInput m ~ s, GrammarConstraint m g, Eq s, FactorialMonoid s) =>
                    g m -> s -> g (ResultFunctor m)
   -- | Given a rank-2 record of parsers and input, produce a record of prefix parses paired with the remaining input
   -- suffix.
   parsePrefix :: (ParserInput m ~ s, GrammarConstraint m g, Eq s, FactorialMonoid s) =>
                  g m -> s -> g (Compose (ResultFunctor m) ((,) s))

-- | Parsers that belong to this class can memoize the parse results to avoid exponential performance complexity.
class MultiParsing m => GrammarParsing m where
   -- | The record of grammar productions associated with the parser
   type ParserGrammar m :: (* -> *) -> *
   -- | For internal use by 'notTerminal'
   type GrammarFunctor m :: * -> *
   -- | Converts the intermediate to final parsing result.
   parsingResult :: ParserInput m -> GrammarFunctor m a -> ResultFunctor m (ParserInput m, a)
   -- | Used to reference a grammar production, only necessary from outside the grammar itself
   nonTerminal :: (g ~ ParserGrammar m, GrammarConstraint m g) => (g (GrammarFunctor m) -> GrammarFunctor m a) -> m a
   -- | Construct a grammar whose every production refers to itself.
   selfReferring :: (g ~ ParserGrammar m, GrammarConstraint m g, Rank2.Distributive g) => g m
   -- | Convert a self-referring grammar function to a grammar.
   fixGrammar :: (g ~ ParserGrammar m, GrammarConstraint m g, Rank2.Distributive g) => (g m -> g m) -> g m
   -- | Mark a parser that relies on primitive recursion to prevent an infinite loop in 'fixGrammar'.
   recursive :: m a -> m a

   selfReferring = Rank2.cotraverse nonTerminal id
   {-# INLINE selfReferring #-}
   fixGrammar = ($ selfReferring)
   {-# INLINE fixGrammar #-}
   recursive = id

class GrammarParsing m => TailsParsing m where
   -- | Parse the tails of the input together with memoized parse results
   parseTails :: GrammarConstraint m g => m r -> [(ParserInput m, g (GrammarFunctor m))] -> GrammarFunctor m r
   parseAllTails :: (GrammarConstraint m g, Rank2.Functor g) =>
                    g m -> [(ParserInput m, g (GrammarFunctor m))] -> [(ParserInput m, g (GrammarFunctor m))]
   parseAllTails _ [] = []
   parseAllTails final parsed@((s, _):_) = (s, gd):parsed
      where gd = Rank2.fmap (`parseTails` parsed) final

-- | Parsers that can produce alternative parses and collect them into an 'Ambiguous' node
class Alternative m => AmbiguousParsing m where
   -- | Collect all alternative parses of the same length into a 'NonEmpty' list of results.
   ambiguous :: m a -> m (Ambiguous a)

-- | If a grammar is 'Lexical', its parsers can instantiate the 'TokenParsing' class.
class (DeterministicParsing m, InputCharParsing m, TokenParsing m) => LexicalParsing m where
   -- | Always succeeds, consuming all white space and comments
   lexicalWhiteSpace :: m ()
   -- | Consumes all whitespace and comments, failing if there are none
   someLexicalSpace :: m ()
   -- | Consumes a single comment, defaults to 'empty'
   lexicalComment :: m ()
   -- | Consumes a single semicolon and any trailing whitespace, returning the character |';'|. The method can be
   -- overridden for automatic semicolon insertion, but if it succeeds on semicolon or white space input it must
   -- consume it.
   lexicalSemicolon :: m Char
   -- | Applies the argument parser and consumes the trailing 'lexicalWhitespace'
   lexicalToken :: m a -> m a
   -- | Applies the argument parser, determines whether its result is a legal identifier, and consumes the trailing
   -- 'lexicalWhitespace'
   identifierToken :: m (ParserInput m) -> m (ParserInput m)
   -- | Determines whether the given character can start an identifier token, allows only a letter or underscore by
   -- default
   isIdentifierStartChar :: Char -> Bool
   -- | Determines whether the given character can be any part of an identifier token, also allows numbers
   isIdentifierFollowChar :: Char -> Bool
   -- | Parses a valid identifier and consumes the trailing 'lexicalWhitespace'
   identifier :: m (ParserInput m)
   -- | Parses the argument word whole, not followed by any identifier character, and consumes the trailing
   -- 'lexicalWhitespace'
   keyword :: ParserInput m -> m ()

   default identifier :: TextualMonoid (ParserInput m) => m (ParserInput m)
   default keyword :: (Show (ParserInput m), TextualMonoid (ParserInput m)) => ParserInput m -> m ()

   lexicalWhiteSpace = takeCharsWhile isSpace *> skipAll (lexicalComment *> takeCharsWhile isSpace)
   someLexicalSpace = takeCharsWhile1 isSpace *> (lexicalComment *> lexicalWhiteSpace <<|> pure ())
                      <<|> lexicalComment *> lexicalWhiteSpace
                      <?> "whitespace"
   lexicalComment = empty
   lexicalSemicolon = lexicalToken (Text.Parser.Char.char ';')
   lexicalToken p = p <* lexicalWhiteSpace
   isIdentifierStartChar c = isLetter c || c == '_'
   isIdentifierFollowChar c = isAlphaNum c || c == '_'
   identifier = identifierToken (liftA2 mappend (satisfyCharInput (isIdentifierStartChar @m))
                                                (takeCharsWhile (isIdentifierFollowChar @m))) <?> "an identifier"
   identifierToken = lexicalToken
   keyword s = lexicalToken (string s *> notSatisfyChar (isIdentifierFollowChar @m)) <?> ("keyword " <> show s)
