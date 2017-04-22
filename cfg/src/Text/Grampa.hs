{-# LANGUAGE FlexibleContexts, KindSignatures, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Classes
   MonoidNull, FactorialMonoid, LeftReductiveMonoid, TextualMonoid,
   GrammarParsing(..), MonoidParsing(..), RecursiveParsing(..),
   -- * Types
   Grammar, GrammarBuilder, AST, Parser, ParseResults(..),
   -- * Grammar and parser manipulation
   fixGrammar, parsePrefix, parseAll, parseSeparated, simpleParse,
   fixGrammarAST,
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
import Text.Grampa.Class (GrammarParsing(..), MonoidParsing(..), RecursiveParsing(..), ParseResults(..))
import Text.Grampa.Parser (Parser(applyParser), ResultList(..))
import Text.Grampa.AST (AST, fixGrammarAST)
import qualified Text.Grampa.Parser as Parser
import qualified Text.Grampa.AST as AST

import Prelude hiding (takeWhile)

type Grammar (g  :: (* -> *) -> *) p s = g (p g s)
type GrammarBuilder (g  :: (* -> *) -> *)
                    (g' :: (* -> *) -> *)
                    (p  :: ((* -> *) -> *) -> * -> * -> *)
                    (s  :: *)
   = g (p g' s) -> g (p g' s)

parsePrefix :: (Rank2.Apply g, Rank2.Traversable g, FactorialMonoid s) =>
               g (AST g s) -> s -> g (Compose ParseResults (Compose [] ((,) s)))
parsePrefix g input = Rank2.fmap (Compose . Parser.fromResultList input) (snd $ head $ parseRecursive g input)

parseAll :: (FactorialMonoid s, Rank2.Traversable g, Rank2.Distributive g, Rank2.Apply g) =>
            g (AST g s) -> s -> g (Compose ParseResults [])
parseAll g input = Rank2.fmap ((snd <$>) . Compose . (getCompose <$>) . Parser.fromResultList input)
                              (snd $ head $ reparse close $ parseRecursive g input)
   where close = Rank2.fmap (<* endOfInput) selfReferring

simpleParse :: FactorialMonoid s => Parser (Rank2.Only r) s r -> s -> ParseResults [(s, r)]
simpleParse p input = getCompose <$> getCompose (Rank2.fromOnly $ Parser.parse (Rank2.Only p) input)

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
                  combine (Const True) (Parsed (_:_)) = Const True
                  combine (Const True) _ = Const False

         recurseOnce s parsedTail initial = Rank2.fmap (($ parsed). applyParser) indirect
            where parsed = (s, initial):parsedTail

-- | Produce a 'Grammar' from its recursive definition
fixGrammar :: Rank2.Distributive g => (g (Parser g i) -> g (Parser g i)) -> g (Parser g i)
fixGrammar gf = gf selfReferring

selfReferring :: Rank2.Distributive g => g (Parser g i)
selfReferring = Rank2.distributeWith nonTerminal id
