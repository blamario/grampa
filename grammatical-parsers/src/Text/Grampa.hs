-- | Collection of parsing algorithms with a common interface, operating on grammars represented as records with rank-2
-- field types.
{-# LANGUAGE FlexibleContexts, KindSignatures, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Parsing methods
   MultiParsing(..),
   simply,
   -- * Types
   Grammar, GrammarBuilder, ParseResults, ParseFailure(..),
   -- * Parser combinators and primitives
   GrammarParsing(..), MonoidParsing(..),
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead)
where

import Text.Parser.Char (CharParsing(char, notChar, anyChar))
import Text.Parser.Combinators (Parsing((<?>), notFollowedBy, skipMany, skipSome, unexpected))
import Text.Parser.LookAhead (LookAheadParsing(lookAhead))

import Data.Functor.Compose (Compose(..))
import qualified Rank2
import Text.Grampa.Class (MultiParsing(..), GrammarParsing(..), MonoidParsing(..), ParseResults, ParseFailure(..))

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
simply :: (Rank2.Only r (p (Rank2.Only r) s) -> s -> Rank2.Only r f)
            -> p (Rank2.Only r) s r -> s -> f r
simply parseGrammar p input = Rank2.fromOnly (parseGrammar (Rank2.Only p) input)
