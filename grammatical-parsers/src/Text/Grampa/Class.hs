{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DefaultSignatures, DeriveDataTypeable, DeriveFunctor,
             FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, OverloadedStrings,
             RankNTypes, ScopedTypeVariables, TypeApplications, TypeFamilies, TypeOperators, TypeSynonymInstances,
             UndecidableInstances #-}
-- | The core classes supported by all the parsers in this library.
module Text.Grampa.Class (MultiParsing(..), GrammarParsing(..),
                          AmbiguousParsing(..), DeterministicParsing(..), InputParsing(..), InputCharParsing(..),
                          CommittedParsing(..), ConsumedInputParsing(..), LexicalParsing(..), TailsParsing(..),
                          ParseResults, ParseFailure(..), FailureDescription(..), Pos,
                          Ambiguous(..), completeParser) where

import Control.Applicative (Alternative(empty), liftA2)
import Data.Char (isAlphaNum, isLetter, isSpace)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Data (Data)
import Data.Typeable (Typeable)
import Data.Monoid (Monoid(mempty, mappend))
import qualified Data.Monoid.Null as Null
import Data.Monoid.Null (MonoidNull)
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)
import Data.Semigroup (Semigroup((<>)))
import Data.Ord (Down(Down))
import Text.Parser.Combinators (Parsing((<?>)))
import Text.Parser.Token (TokenParsing)
import Text.Parser.Deterministic (DeterministicParsing(..))
import Text.Parser.Input (ConsumedInputParsing(..), InputParsing(..), InputCharParsing(..))
import qualified Text.Parser.Char
import Data.Kind (Constraint)

import qualified Rank2

import Prelude hiding (takeWhile)

type ParseResults s = Either (ParseFailure Pos s)

-- | A 'ParseFailure' contains the offset of the parse failure and the list of things expected at that offset.
data ParseFailure pos s =
   ParseFailure {failurePosition :: pos,
                 expectedAlternatives :: [FailureDescription s],  -- ^ expected input alternatives
                 errorAlternatives ::    [FailureDescription s]   -- ^ erroneous input descriptions
                }
   deriving (Eq, Functor, Show)

-- | A position in the input is represented as the length of its remainder.
type Pos = Down Int

-- | An expected or erroneous input can be described using 'String' or using the input type
data FailureDescription s = StaticDescription String   -- ^ a readable description of the expected input
                          | LiteralDescription s       -- ^ a literal piece of expected input
                            deriving (Functor, Eq, Ord, Read, Show)

instance (Ord pos, Ord s) => Semigroup (ParseFailure pos s) where
   f1@(ParseFailure pos1 exp1 err1) <> f2@(ParseFailure pos2 exp2 err2) = ParseFailure pos' exp' err'
      where ParseFailure pos' exp' err'
              | pos1 > pos2 = f1
              | pos1 < pos2 = f2
              | otherwise = ParseFailure pos1 (merge exp1 exp2) (merge err1 err2)
            merge [] xs = xs
            merge xs [] = xs
            merge xs@(x:xs') ys@(y:ys')
               | x < y = x : merge xs' ys
               | x > y = y : merge xs ys'
               | otherwise = x : merge xs' ys'

instance Ord s => Monoid (ParseFailure Pos s) where
   mempty = ParseFailure (Down maxBound) [] []
   mappend = (<>)

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
   mappend = (<>)

completeParser :: MonoidNull s => Compose (ParseResults s) (Compose [] ((,) s)) r -> Compose (ParseResults s) [] r
completeParser (Compose (Left failure)) = Compose (Left failure)
completeParser (Compose (Right (Compose results))) =
   case filter (Null.null . fst) results
   of [] -> Compose (Left $ ParseFailure 0 [StaticDescription "a complete parse"] [])
      completeResults -> Compose (Right $ snd <$> completeResults)

-- | Choose one of the instances of this class to parse with.
class InputParsing m => MultiParsing m where
   -- | Some parser types produce a single result, others a list of results.
   type ResultFunctor m :: Type -> Type
   type GrammarConstraint m (g :: (Type -> Type) -> Type) :: Constraint
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
   type ParserGrammar m :: (Type -> Type) -> Type
   -- | For internal use by 'notTerminal'
   type GrammarFunctor m :: Type -> Type
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
   -- | Convert a left-recursive parser to a non-left-recursive one. For example, you can replace the left-recursive
   -- production
   --
   -- > foo = BinOp <$> foo <*> bar <|> baz
   --
   -- in the field @foo@ of grammar @g@ with
   --
   -- > foo = chainRecursive (\x g-> g{foo = x}) baz (BinOp <$> foo <*> bar)
   --
   -- This method works on individual parsers left-recursive on themselves, not on grammars with mutually
   -- left-recursive productions. Use "Text.Grampa.ContextFree.Memoizing.LeftRecursive" for the latter.
   chainRecursive :: (g ~ ParserGrammar m, f ~ GrammarFunctor m, GrammarConstraint m g)
                  => (f a -> g f -> g f) -- ^ setter for the parsed results of each iteration
                  -> m a -- ^ the non-recursive base case
                  -> m a -- ^ the recursive case to iterate
                  -> m a
   -- | Line 'chainRecursive' but produces only the longest possible parse. The modified example
   --
   -- > foo = chainLongestRecursive (\x g-> g{foo = x}) baz (BinOp <$> foo <*> bar)
   --
   -- would be equivalent to the left-recursive production with biased choice
   --
   -- > foo = BinOp <$> foo <*> bar <<|> baz
   chainLongestRecursive :: (g ~ ParserGrammar m, f ~ GrammarFunctor m, GrammarConstraint m g)
                         => (f a -> g f -> g f) -- ^ setter for the parsed results of each iteration
                         -> m a -- ^ the non-recursive base case
                         -> m a -- ^ the recursive case to iterate
                         -> m a

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

-- | Parsers that can temporarily package and delay failure, in a way dual to Parsec's @try@ combinator. Where Parsec
-- would require something like
--
-- > alternatives  =  try intro1 *> expected1
-- >              <|> try intro2 *> expected2
-- >              <|> fallback
--
-- you can instead say
--
-- > alternatives = admit  $  intro1 *> commit expected1
-- >                      <|> intro2 *> commit expected2
-- >                      <|> commit fallback
--
-- A parsing failure inside an @intro@ parser leaves the other alternatives open, a failure inside an @expected@
-- parser bubbles up and out of the whole @admit@ block.
class Alternative m => CommittedParsing m where
   type CommittedResults m :: Type -> Type
   -- | Commits the argument parser to success.
   commit :: m a -> m (CommittedResults m a)
   -- | Admits a possible defeat of the argument parser.
   admit :: m (CommittedResults m a) -> m a
  
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
