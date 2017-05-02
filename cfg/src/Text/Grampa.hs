{-# LANGUAGE FlexibleContexts, KindSignatures, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Classes
   MonoidNull, FactorialMonoid, LeftReductiveMonoid, TextualMonoid,
   GrammarParsing(..), MonoidParsing(..), RecursiveParsing(..),
   -- * Types
   Grammar, GrammarBuilder, AST, Parallel.Parser, ParseResults, ParseFailure(..),
   -- * Grammar and parser manipulation
   parsePEG, parsePackrat, parseParallel, parsePrefix, parseAll, parseSeparated, simply, parseShared,
   -- * Parser combinators
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead)
where

import Control.Applicative

import Data.Monoid (Any(..), (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid)
import Data.Monoid.Null (MonoidNull)
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)

import qualified Data.Monoid.Factorial as Factorial

import Text.Parser.Char (CharParsing(char, notChar, anyChar))
import Text.Parser.Combinators (Parsing((<?>), notFollowedBy, skipMany, skipSome, unexpected))
import Text.Parser.LookAhead (LookAheadParsing(lookAhead))

import Data.Functor.Compose (Compose(..))
import qualified Rank2
import Text.Grampa.Class (GrammarParsing(..), MonoidParsing(..), RecursiveParsing(..), ParseResults, ParseFailure(..))
import Text.Grampa.Parser (Parser(applyParser), ResultList(..))
import Text.Grampa.AST (AST)
import qualified Text.Grampa.PEG.Backtrack as PEG
import qualified Text.Grampa.PEG.Packrat as Packrat
import qualified Text.Grampa.ContextFree.Parallel as Parallel
import qualified Text.Grampa.Parser as Parser
import qualified Text.Grampa.AST as AST

import Prelude hiding (takeWhile)

type Grammar (g  :: (* -> *) -> *) p s = g (p g s)
type GrammarBuilder (g  :: (* -> *) -> *)
                    (g' :: (* -> *) -> *)
                    (p  :: ((* -> *) -> *) -> * -> * -> *)
                    (s  :: *)
   = g (p g' s) -> g (p g' s)

-- | Parse the given input against the given Parsing Expression Grammar using a backtracking algorithm, very fast for
-- grammars in LL(1) class but with potentially exponential performance for longer ambiguous prefixes.
parsePEG :: (Rank2.Functor g, FactorialMonoid s) => g (PEG.Parser g s) -> s -> g (Compose ParseResults ((,) s))
parsePEG = PEG.parse

-- | Parse the given input against the given Parsing Expression Grammar using a packrat algorithm, with O(1) performance
-- bounds but with worse constants and more memory consumption than 'parsePEG'.
parsePackrat :: (Rank2.Functor g, FactorialMonoid s) => g (Packrat.Parser g s) -> s -> g (Compose ParseResults ((,) s))
parsePackrat = Packrat.parse

-- | Parse the given input against the given context-free grammar using a parallel parsing algorithm with no result
-- sharing nor left recursion support. The function returns a list of all possible input prefix parses paired with the
-- remaining input suffix.
parseParallel :: (Rank2.Functor g, FactorialMonoid s) =>
                 g (Parallel.Parser g s) -> s -> g (Compose ParseResults (Compose [] ((,) s)))
parseParallel = Parallel.parse

-- | Parse the given input against the given context-free grammar with packrat-like sharing of parse results. Left
-- recursive grammars are not supported. The function returns a list of all possible input prefix parses paired with the
-- remaining input suffix.
parseShared :: (Rank2.Functor g, FactorialMonoid s) =>
               g (Parser g s) -> s -> g (Compose ParseResults (Compose [] ((,) s)))
parseShared = Parser.parse

-- | Parse the given input against the given general context-free grammar using a generalized packrat algorithm,
-- returning a list of all possible parses of an input prefix paired with the remaining input suffix.
parsePrefix :: (Rank2.Apply g, Rank2.Traversable g, FactorialMonoid s) =>
               g (AST g s) -> s -> g (Compose ParseResults (Compose [] ((,) s)))
parsePrefix g input = Rank2.fmap (Compose . Parser.fromResultList input) (snd $ head $ parseRecursive g input)

-- | Parse the given input against the given general context-free grammar using a generalized packrat algorithm,
-- returning a list of all possible parses that consume the entire input.
parseAll :: (FactorialMonoid s, Rank2.Traversable g, Rank2.Distributive g, Rank2.Apply g) =>
            g (AST g s) -> s -> g (Compose ParseResults [])
parseAll g input = Rank2.fmap ((snd <$>) . Compose . (getCompose <$>) . Parser.fromResultList input)
                              (snd $ head $ reparse close $ parseRecursive g input)
   where close = Rank2.fmap (<* endOfInput) selfReferring

-- | Apply the given parse function like 'parsePEG' or 'parseParallel' to the given simple grammar-free parser and its
-- input.
simply :: (Rank2.Only r (p (Rank2.Only r) s) -> s -> Rank2.Only r (Compose ParseResults f))
            -> p (Rank2.Only r) s r -> s -> ParseResults (f r)
simply parse p input = getCompose (Rank2.fromOnly $ parse (Rank2.Only p) input)

reparse :: Rank2.Functor g => g (Parser g s) -> [(s, g (ResultList g s))] -> [(s, g (ResultList g s))]
reparse _ [] = []
reparse final parsed@((s, _):_) = (s, gd):parsed
   where gd = Rank2.fmap (`applyParser` parsed) final

newtype Couple f a = Couple{unCouple :: (f a, f a)} deriving Show

parseRecursive :: forall g s. (Rank2.Apply g, Rank2.Traversable g, FactorialMonoid s) =>
                  g (AST g s) -> s -> [(s, g (ResultList g s))]
parseRecursive ast = parseSeparated descendants (Rank2.fmap AST.toParser indirect) (Rank2.fmap AST.toParser direct)
   where directRecursive = Rank2.fmap (Couple . AST.splitDirect) ast
         cyclicDescendants = AST.leftDescendants ast
         cyclic = Rank2.fmap (mapConst fst) cyclicDescendants
         descendants = Rank2.liftA3 cond cyclic (Rank2.fmap (mapConst snd) cyclicDescendants) noDescendants
         direct = Rank2.liftA3 cond cyclic (Rank2.fmap (fst . unCouple) directRecursive) ast
         indirect = Rank2.liftA3 cond cyclic (Rank2.fmap (snd . unCouple) directRecursive) emptyGrammar
         emptyGrammar :: g (AST g s)
         emptyGrammar = Rank2.fmap (const empty) ast
         noDescendants = Rank2.fmap (const $ Const $ Rank2.fmap (const $ Const False) ast) ast
         cond (Const False) _t f = f
         cond (Const True) t _f = t
         mapConst f (Const c) = Const (f c)

-- | Parse the given input using a context-free grammar separated into two parts: the first specifying all the
-- left-recursive productions, the second all others. The first function argument specifies the left-recursive
-- dependencies among the grammar productions.
parseSeparated :: forall g s. (Rank2.Apply g, Rank2.Foldable g, FactorialMonoid s) =>
                  g (Const (g (Const Bool))) -> g (Parser g s) -> g (Parser g s) -> s -> [(s, g (ResultList g s))]
parseSeparated dependencies indirect direct input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d'):parsedTail
                  d      = Rank2.fmap (($ (s,d):parsedTail) . applyParser) direct
                  d'     = fixRecursive s parsedTail d

         fixRecursive :: s -> [(s, g (ResultList g s))] -> g (ResultList g s) -> g (ResultList g s)
         whileAnyContinues :: g (ResultList g s) -> g (ResultList g s) -> g (ResultList g s)
         recurseOnce :: s -> [(s, g (ResultList g s))] -> g (ResultList g s) -> g (ResultList g s)

         fixRecursive s parsedTail initial =
            foldr1 whileAnyContinues (iterate (recurseOnce s parsedTail) initial)

         whileAnyContinues g1 g2 = Rank2.liftA3 choiceWhile dependencies g1 g2
            where choiceWhile :: Const (g (Const Bool)) x -> ResultList g i x -> ResultList g i x -> ResultList g i x
                  combine :: Const Bool x -> ResultList g i x -> Const Bool x
                  choiceWhile (Const deps) r1 r2
                     | getAny (Rank2.foldMap (Any . getConst) (Rank2.liftA2 combine deps g1)) = r1 <> r2
                     | otherwise = r1
                  combine (Const False) _ = Const False
                  combine (Const True) (ResultList [] _) = Const False
                  combine (Const True) _ = Const True

         recurseOnce s parsedTail initial = Rank2.fmap (($ parsed). applyParser) indirect
            where parsed = (s, initial):parsedTail
