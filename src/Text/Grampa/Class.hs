module Text.Grampa.Class (MonoidParsing(..)) where

import Control.Applicative (Alternative(many))
import Data.Char (isSpace)
import Data.Monoid (Monoid)
import Data.Monoid.Cancellative (LeftReductiveMonoid)
import Data.Monoid.Null (MonoidNull)
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid(singleton))

class MonoidParsing m where
   infixl 3 <<|>
   (<<|>) :: m s r -> m s r -> m s r
   -- | A parser that fails on any input and succeeds at its end.
   endOfInput :: MonoidNull s => m s ()
   -- | Always sucessful parser that returns the remaining input without consuming it.
   getInput :: MonoidNull s => m s s

   -- | A parser that accepts any single input atom.
   anyToken :: FactorialMonoid s => m s s
   -- | A parser that accepts a specific input atom.
   token :: (Eq s, FactorialMonoid s) => s -> m s s
   -- | A parser that accepts an input atom only if it satisfies the given predicate.
   satisfy :: FactorialMonoid s => (s -> Bool) -> m s s
   -- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the
   -- given predicate.
   satisfyChar :: TextualMonoid s => (Char -> Bool) -> m s Char

   -- | A stateful scanner.  The predicate consumes and transforms a state argument, and each transformed state is
   -- passed to successive invocations of the predicate on each token of the input until one returns 'Nothing' or the
   -- input ends.
   --
   -- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first
   -- character.
   --
   -- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
   -- until a failure occurs.  Careless use will thus result in an infinite loop.
   scan :: FactorialMonoid t => s -> (s -> t -> Maybe s) -> m t t
   -- | Stateful scanner like `scanChars`, but specialized for 'TextualMonoid' inputs.
   scanChars :: TextualMonoid t => s -> (s -> Char -> Maybe s) -> m t t
   -- | A parser that consumes and returns the given prefix of the input.
   string :: (FactorialMonoid s, LeftReductiveMonoid s, Show s) => s -> m s s

   -- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
   -- 'concatMany . satisfy'.
   --
   -- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
   -- until a failure occurs.  Careless use will thus result in an infinite loop.
   takeWhile :: FactorialMonoid s => (s -> Bool) -> m s s
   -- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
   -- version of 'concatSome . satisfy'.
   takeWhile1 :: FactorialMonoid s => (s -> Bool) -> m s s
   -- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
   -- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
   --
   -- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
   -- until a failure occurs.  Careless use will thus result in an infinite loop.
   takeCharsWhile :: TextualMonoid s => (Char -> Bool) -> m s s
   -- | Specialization of 'takeWhile1' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
   -- match the given predicate; an optimized version of 'concatSome . satisfyChar'.
   takeCharsWhile1 :: TextualMonoid s => (Char -> Bool) -> m s s
   -- | Consume all whitespace characters.
   whiteSpace :: TextualMonoid s => m s ()
   -- | Zero or more argument occurrences like 'many', with concatenated monoidal results.
   concatMany :: Monoid a => m s a -> m s a

   token x = satisfy (== x)
