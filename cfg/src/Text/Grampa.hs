{-# LANGUAGE FlexibleContexts, KindSignatures, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Classes
   MultiParsing(..), GrammarParsing(..), MonoidParsing(..), RecursiveParsing(..),
   -- * Types
   Grammar, GrammarBuilder, ParseResults, ParseFailure(..),
   -- * Grammar and parser manipulation
   parseComplete, parsePrefix, simply,
   -- * Parser combinators
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead)
where

import Text.Parser.Char (CharParsing(char, notChar, anyChar))
import Text.Parser.Combinators (Parsing((<?>), notFollowedBy, skipMany, skipSome, unexpected))
import Text.Parser.LookAhead (LookAheadParsing(lookAhead))

import Data.Functor.Compose (Compose(..))
import qualified Rank2
import Text.Grampa.Class (MultiParsing(..), GrammarParsing(..), MonoidParsing(..), RecursiveParsing(..),
                          ParseResults, ParseFailure(..))
import Text.Grampa.ContextFree.LeftRecursive (parseComplete, parsePrefix)

import Prelude hiding (takeWhile)

type Grammar (g  :: (* -> *) -> *) p s = g (p g s)
type GrammarBuilder (g  :: (* -> *) -> *)
                    (g' :: (* -> *) -> *)
                    (p  :: ((* -> *) -> *) -> * -> * -> *)
                    (s  :: *)
   = g (p g' s) -> g (p g' s)

-- | Apply the given 'parse' function to the given grammar-free parser and its input.
simply :: (Rank2.Only r (p (Rank2.Only r) s) -> s -> Rank2.Only r (Compose ParseResults f))
            -> p (Rank2.Only r) s r -> s -> ParseResults (f r)
simply parseGrammar p input = getCompose (Rank2.fromOnly $ parseGrammar (Rank2.Only p) input)
