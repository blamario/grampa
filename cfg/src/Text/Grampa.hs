{-# LANGUAGE FlexibleContexts, KindSignatures, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Classes
   MultiParsing(..), GrammarParsing(..), MonoidParsing(..), RecursiveParsing(..),
   -- * Types
   Grammar, GrammarBuilder, AST, ParseResults, ParseFailure(..),
   -- * Grammar and parser manipulation
   parsePrefix, parseAll, parseSeparated, simply,
   -- * Parser combinators
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead)
where

import Control.Applicative

import Data.Monoid.Factorial (FactorialMonoid)

import Text.Parser.Char (CharParsing(char, notChar, anyChar))
import Text.Parser.Combinators (Parsing((<?>), notFollowedBy, skipMany, skipSome, unexpected))
import Text.Parser.LookAhead (LookAheadParsing(lookAhead))

import Data.Functor.Compose (Compose(..))
import qualified Rank2
import Text.Grampa.Class (MultiParsing(..), GrammarParsing(..), MonoidParsing(..), RecursiveParsing(..),
                          ParseResults, ParseFailure(..))
import Text.Grampa.Parser (Parser(applyParser), ResultList(..), fromResultList)
import Text.Grampa.AST (AST, parsePrefix, parseRecursive, parseSeparated)

import Prelude hiding (takeWhile)

type Grammar (g  :: (* -> *) -> *) p s = g (p g s)
type GrammarBuilder (g  :: (* -> *) -> *)
                    (g' :: (* -> *) -> *)
                    (p  :: ((* -> *) -> *) -> * -> * -> *)
                    (s  :: *)
   = g (p g' s) -> g (p g' s)

-- | Parse the given input against the given general context-free grammar using a generalized packrat algorithm,
-- returning a list of all possible parses that consume the entire input.
parseAll :: (FactorialMonoid s, Rank2.Traversable g, Rank2.Distributive g, Rank2.Apply g) =>
            g (AST g s) -> s -> g (Compose ParseResults [])
parseAll g input = Rank2.fmap ((snd <$>) . Compose . (getCompose <$>) . fromResultList input)
                              (snd $ head $ reparse close $ parseRecursive g input)
   where close = Rank2.fmap (<* endOfInput) selfReferring

-- | Apply the given 'parse' function to the given grammar-free parser and its input.
simply :: (Rank2.Only r (p (Rank2.Only r) s) -> s -> Rank2.Only r (Compose ParseResults f))
            -> p (Rank2.Only r) s r -> s -> ParseResults (f r)
simply parseGrammar p input = getCompose (Rank2.fromOnly $ parseGrammar (Rank2.Only p) input)

reparse :: Rank2.Functor g => g (Parser g s) -> [(s, g (ResultList g s))] -> [(s, g (ResultList g s))]
reparse _ [] = []
reparse final parsed@((s, _):_) = (s, gd):parsed
   where gd = Rank2.fmap (`applyParser` parsed) final
