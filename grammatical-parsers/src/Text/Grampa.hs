-- | A collection of parsing algorithms with a common interface, operating on grammars represented as records with
-- rank-2 field types.
{-# LANGUAGE FlexibleContexts, KindSignatures, OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Applying parsers
   failureDescription, simply,
   -- * Types
   Grammar, GrammarBuilder, ParseResults, ParseFailure(..), Expected(..), Ambiguous(..), Position,
   -- * Classes and combinators
   -- ** Parsing classes
   DeterministicParsing(..), AmbiguousParsing(..),
   LexicalParsing(..),
   -- ** Grammars
   MultiParsing(..), GrammarParsing(..),
   -- ** From the [input-parsers](http://hackage.haskell.org/package/input-parsers) library
   InputParsing(..), InputCharParsing(..), ConsumedInputParsing(..),
   -- ** From the [parsers](http://hackage.haskell.org/package/parsers) library
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead,
   TokenParsing(..),
   -- ** Other combinators
   module Text.Grampa.Combinators)
where

import Data.List (intersperse, nub, sort)
import Data.Monoid ((<>))
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
                          ConsumedInputParsing(..), DeterministicParsing(..), LexicalParsing(..),
                          AmbiguousParsing(..), Ambiguous(..), ParseResults, ParseFailure(..), Expected(..))

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
failureDescription :: forall s. (Ord s, TextualMonoid s) => s -> ParseFailure s -> Int -> s
failureDescription input (ParseFailure pos expected) contextLineCount =
   Position.context input (Position.fromStart pos) contextLineCount
   <> "expected " <> oxfordComma (fromExpected <$> nub (sort expected))
   where oxfordComma :: [s] -> s
         oxfordComma [] = ""
         oxfordComma [x] = x
         oxfordComma [x, y] = x <> " or " <> y
         oxfordComma (x:y:rest) = mconcat (intersperse ", " (x : y : onLast ("or " <>) rest))
         onLast _ [] = []
         onLast f [x] = [f x]
         onLast f (x:xs) = x : onLast f xs
         fromExpected (Expected s) = fromString s
         fromExpected (ExpectedInput s) = "string \"" <> s <> "\""
