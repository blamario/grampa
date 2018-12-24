-- | Collection of parsing algorithms with a common interface, operating on grammars represented as records with rank-2
-- field types.
{-# LANGUAGE FlexibleContexts, KindSignatures, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Parsing methods
   MultiParsing(..),
   showFailure, simply,
   -- * Types
   Grammar, GrammarBuilder, ParseResults, ParseFailure(..), Ambiguous(..),
   -- * Parser combinators and primitives
   GrammarParsing(..), MonoidParsing(..), AmbiguousParsing(..), Lexical(..),
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead)
where

import Data.List (intercalate)
import Data.Monoid ((<>))
import Data.Monoid.Textual (TextualMonoid, toString)
import Text.Parser.Char (CharParsing(char, notChar, anyChar))
import Text.Parser.Combinators (Parsing((<?>), notFollowedBy, skipMany, skipSome, unexpected))
import Text.Parser.LookAhead (LookAheadParsing(lookAhead))

import qualified Rank2
import Text.Grampa.Class (Lexical(..), MultiParsing(..), GrammarParsing(..), MonoidParsing(..), AmbiguousParsing(..),
                          Ambiguous(..), ParseResults, ParseFailure(..))

-- | A type synonym for a fixed grammar record type @g@ with a given parser type @p@ on input streams of type @s@
type Grammar (g  :: (* -> *) -> *) p s = g (p g s)

-- | A type synonym for an endomorphic function on a grammar record type @g@, whose parsers of type @p@ build grammars
-- of type @g'@, parsing input streams of type @s@
type GrammarBuilder (g  :: (* -> *) -> *)
                    (g' :: (* -> *) -> *)
                    (p  :: ((* -> *) -> *) -> * -> * -> *)
                    (s  :: *)
   = g (p g' s) -> g (p g' s)

-- | Apply the given 'parse' function to the given grammar-free parser and its input.
simply :: (Rank2.Only r (p (Rank2.Only r) s) -> s -> Rank2.Only r f) -> p (Rank2.Only r) s r -> s -> f r
simply parseGrammar p input = Rank2.fromOnly (parseGrammar (Rank2.Only p) input)

-- | Given the textual parse input, the parse failure on the input, and the number of lines preceding the failure to
-- show, produce a human-readable failure description.
showFailure :: TextualMonoid s => s -> ParseFailure -> Int -> String
showFailure input (ParseFailure pos expected) preceding =
   unlines prevLines <> replicate column ' ' <> "^\n"
   <> "at line " <> show (length allPrevLines) <> ", column " <> show (column+1) <> "\n"
   <> "expected " <> oxfordComma expected
   where oxfordComma [] = []
         oxfordComma [x] = x
         oxfordComma [x, y] = x <> " or " <> y
         oxfordComma (x:y:rest) = intercalate ", " (x : y : onLast ("or " <>) rest)
         onLast _ [] = []
         onLast f [x] = [f x]
         onLast f (x:xs) = x : onLast f xs
         (allPrevLines, column) = context [] pos (lines $ toString (const mempty) input)
         prevLines = reverse (take (succ preceding) allPrevLines)
         context revLines restCount []
            | restCount > 0 = (["Error: the failure position is beyond the input length"], -1)
            | otherwise = (revLines, restCount)
         context revLines restCount (next:rest)
            | restCount' < 0 = (next:revLines, restCount)
            | otherwise = context (next:revLines) restCount' rest
            where nextLength = length next
                  restCount' = restCount - nextLength - 1
