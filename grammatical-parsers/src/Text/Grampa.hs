-- | A collection of parsing algorithms with a common interface, operating on grammars represented as records with
-- rank-2 field types.
{-# LANGUAGE FlexibleContexts, KindSignatures, OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Applying parsers
   failureDescription, simply,
   -- * Types
   Grammar, GrammarBuilder, ParseResults, ParseFailure(..), FailureDescription(..), Ambiguous(..), Pos,
   -- * Classes
   -- ** Parsing
   DeterministicParsing(..), AmbiguousParsing(..), CommittedParsing(..), TraceableParsing(..),
   LexicalParsing(..),
   -- ** Grammars
   MultiParsing(..), GrammarParsing(..),
   -- ** From the [input-parsers](http://hackage.haskell.org/package/input-parsers) library
   InputParsing(..), InputCharParsing(..), ConsumedInputParsing(..), Position(..),
   -- ** From the [parsers](http://hackage.haskell.org/package/parsers) library
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead,
   TokenParsing(..),
   -- * Other combinators
   module Text.Grampa.Combinators)
where

import Data.List (intersperse)
import Data.Monoid ((<>))
import Data.Monoid.Factorial (drop)
import Data.Monoid.Null (null)
import Data.Monoid.Textual (TextualMonoid)
import Data.String (IsString(fromString))
import Text.Parser.Char (CharParsing(char, notChar, anyChar))
import Text.Parser.Combinators (Parsing((<?>), notFollowedBy, skipMany, skipSome, unexpected))
import Text.Parser.LookAhead (LookAheadParsing(lookAhead))
import Text.Parser.Token (TokenParsing(..))
import Text.Parser.Input.Position (Position)
import qualified Text.Parser.Input.Position as Position
import Text.Grampa.Combinators (concatMany, concatSome)

import qualified Rank2
import Text.Grampa.Class (MultiParsing(..), GrammarParsing(..),
                          InputParsing(..), InputCharParsing(..),
                          ConsumedInputParsing(..), LexicalParsing(..),
                          CommittedParsing(..), DeterministicParsing(..),
                          AmbiguousParsing(..), Ambiguous(..),
                          ParseResults, ParseFailure(..), FailureDescription(..), Pos)
import Text.Grampa.Internal (TraceableParsing(..))

import Prelude hiding (drop, null)

-- | A type synonym for a fixed grammar record type @g@ with a given parser type @p@ on input streams of type @s@
type Grammar (g  :: (* -> *) -> *) p s = g (p g s)

-- | A type synonym for an endomorphic function on a grammar record type @g@, whose parsers of type @p@ build grammars
-- of type @g'@, parsing input streams of type @s@
type GrammarBuilder (g  :: (* -> *) -> *)
                    (g' :: (* -> *) -> *)
                    (p  :: ((* -> *) -> *) -> * -> * -> *)
                    (s  :: *)
   = g (p g' s) -> g (p g' s)

-- | Apply the given parsing function (typically `parseComplete` or `parsePrefix`) to the given grammar-agnostic
-- parser and its input. A typical invocation might be
--
-- > getCompose $ simply parsePrefix myParser myInput
simply :: (Rank2.Only r (p (Rank2.Only r) s) -> s -> Rank2.Only r f) -> p (Rank2.Only r) s r -> s -> f r
simply parseGrammar p input = Rank2.fromOnly (parseGrammar (Rank2.Only p) input)

-- | Given the textual parse input, the parse failure on the input, and the number of lines preceding the failure to
-- show, produce a human-readable failure description.
failureDescription :: forall s pos. (Ord s, TextualMonoid s, Position pos) => s -> ParseFailure pos s -> Int -> s
failureDescription input (ParseFailure pos expected erroneous) contextLineCount =
   Position.context input pos contextLineCount
   <> mconcat
      (intersperse ", but " $ filter (not . null)
       [onNonEmpty ("expected " <>) $ oxfordComma " or " (fromDescription <$> expected),
        oxfordComma " and " (fromDescription <$> erroneous)])
   where oxfordComma :: s -> [s] -> s
         oxfordComma _ [] = ""
         oxfordComma _ [x] = x
         oxfordComma conjunction [x, y] = x <> conjunction <> y
         oxfordComma conjunction (x:y:rest) = mconcat (intersperse ", " (x : y : onLast (drop 1 conjunction <>) rest))
         onNonEmpty f x = if null x then x else f x
         onLast _ [] = []
         onLast f [x] = [f x]
         onLast f (x:xs) = x : onLast f xs
         fromDescription (StaticDescription s) = fromString s
         fromDescription (LiteralDescription s) = "string \"" <> s <> "\""
