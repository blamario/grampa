{-# LANGUAGE ConstraintKinds, RankNTypes, TypeFamilies #-}
module Text.Grampa.Class (MultiParsing(..), AmbiguousParsing(..), GrammarParsing(..), MonoidParsing(..),
                          ParseResults, ParseFailure(..), Ambiguous(..), completeParser) where

import Data.Functor.Compose (Compose(..))
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid (Monoid)
import Data.Monoid.Cancellative (LeftReductiveMonoid)
import qualified Data.Monoid.Null as Null
import Data.Monoid.Null (MonoidNull)
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)
import GHC.Exts (Constraint)

import qualified Rank2

type ParseResults = Either ParseFailure

-- | A 'ParseFailure' contains the offset of the parse failure and the list of things expected at that offset. 
data ParseFailure = ParseFailure Int [String] deriving (Eq, Show)

newtype Ambiguous a = Ambiguous (NonEmpty a)

completeParser :: MonoidNull s => Compose ParseResults (Compose [] ((,) s)) r -> Compose ParseResults [] r
completeParser (Compose (Left failure)) = Compose (Left failure)
completeParser (Compose (Right (Compose results))) =
   case filter (Null.null . fst) results
   of [] -> Compose (Left $ ParseFailure 0 ["complete parse"])
      completeResults -> Compose (Right $ snd <$> completeResults)

-- | Choose one of the instances of this class to parse with.
class MultiParsing m where
   -- | Some parser types produce a single result, others a list of results.
   type ResultFunctor m :: * -> *
   type GrammarConstraint m (g :: (* -> *) -> *) :: Constraint
   type GrammarConstraint m g = Rank2.Functor g
   -- | Given a rank-2 record of parsers and input, produce a record of parses of the complete input.
   parseComplete :: (GrammarConstraint m g, FactorialMonoid s) => g (m g s) -> s -> g (ResultFunctor m)
   -- | Given a rank-2 record of parsers and input, produce a record of prefix parses paired with the remaining input
   -- suffix.
   parsePrefix :: (GrammarConstraint m g, FactorialMonoid s) =>
                  g (m g s) -> s -> g (Compose (ResultFunctor m) ((,) s))

-- | Parsers that belong to this class memoize the parse results to avoid exponential performance complexity.
class MultiParsing m => GrammarParsing m where
   type GrammarFunctor m :: ((* -> *) -> *) -> * -> * -> *
   -- | Used to reference a grammar production, only necessary from outside the grammar itself
   nonTerminal :: GrammarConstraint m g => (g (GrammarFunctor m g s) -> GrammarFunctor m g s a) -> m g s a
   -- | Construct a grammar whose every production refers to itself.
   selfReferring :: (GrammarConstraint m g, Rank2.Distributive g) => g (m g s)
   -- | Convert a self-referring grammar function to a grammar.
   fixGrammar :: forall g s. (GrammarConstraint m g, Rank2.Distributive g) => (g (m g s) -> g (m g s)) -> g (m g s)
   -- | Mark a parser that relies on primitive recursion to prevent an infinite loop in 'fixGrammar'.
   recursive :: m g s a -> m g s a

   selfReferring = Rank2.cotraverse nonTerminal id
   fixGrammar = ($ selfReferring)
   recursive = id

-- | Methods for parsing monoidal inputs
class MonoidParsing m where
   -- | A parser that fails on any input and succeeds at its end.
   endOfInput :: FactorialMonoid s => m s ()
   -- | Always sucessful parser that returns the remaining input without consuming it.
   getInput :: FactorialMonoid s => m s s

   -- | A parser that accepts any single input atom.
   anyToken :: FactorialMonoid s => m s s
   -- | A parser that accepts a specific input atom.
   token :: (Eq s, FactorialMonoid s) => s -> m s s
   -- | A parser that accepts an input atom only if it satisfies the given predicate.
   satisfy :: FactorialMonoid s => (s -> Bool) -> m s s
   -- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting and returning an input character only if it
   -- satisfies the given predicate.
   satisfyChar :: TextualMonoid s => (Char -> Bool) -> m s Char
   -- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the
   -- given predicate, and returning the input atom that represents the character. A faster version of @singleton <$>
   -- satisfyChar p@ and of @satisfy (fromMaybe False p . characterPrefix)@.
   satisfyCharInput :: TextualMonoid s => (Char -> Bool) -> m s s
   -- | A parser that succeeds exactly when satisfy doesn't, equivalent to @notFollowedBy . satisfy@
   notSatisfy :: FactorialMonoid s => (s -> Bool) -> m s ()
   -- | A parser that succeeds exactly when satisfyChar doesn't, equivalent to @notFollowedBy . satisfyChar@
   notSatisfyChar :: TextualMonoid s => (Char -> Bool) -> m s ()

   -- | A stateful scanner. The predicate modifies a state argument, and each transformed state is passed to successive
   -- invocations of the predicate on each token of the input until one returns 'Nothing' or the input ends.
   --
   -- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first
   -- character.
   --
   -- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers
   -- loop until a failure occurs.  Careless use will thus result in an infinite loop.
   scan :: FactorialMonoid t => s -> (s -> t -> Maybe s) -> m t t
   -- | Stateful scanner like `scanChars`, but specialized for 'TextualMonoid' inputs.
   scanChars :: TextualMonoid t => s -> (s -> Char -> Maybe s) -> m t t
   -- | A parser that consumes and returns the given prefix of the input.
   string :: (FactorialMonoid s, LeftReductiveMonoid s, Show s) => s -> m s s

   -- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
   -- 'concatMany . satisfy'.
   --
   -- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers
   -- loop until a failure occurs.  Careless use will thus result in an infinite loop.
   takeWhile :: FactorialMonoid s => (s -> Bool) -> m s s
   -- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
   -- version of 'concatSome . satisfy'.
   takeWhile1 :: FactorialMonoid s => (s -> Bool) -> m s s
   -- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
   -- match the given predicate; an optimized version of 'fmap fromString  . many . satisfyChar'.
   --
   -- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers
   -- loop until a failure occurs.  Careless use will thus result in an infinite loop.
   takeCharsWhile :: TextualMonoid s => (Char -> Bool) -> m s s
   -- | Specialization of 'takeWhile1' on 'TextualMonoid' inputs, accepting the longest sequence of input characters
   -- that match the given predicate; an optimized version of 'fmap fromString  . some . satisfyChar'.
   takeCharsWhile1 :: TextualMonoid s => (Char -> Bool) -> m s s
   -- | Consume all whitespace characters.
   whiteSpace :: TextualMonoid s => m s ()
   -- | Zero or more argument occurrences like 'many', with concatenated monoidal results.
   concatMany :: Monoid a => m s a -> m s a

   token x = satisfy (== x)

class AmbiguousParsing m where
   ambiguous :: m a -> m (Ambiguous a)
