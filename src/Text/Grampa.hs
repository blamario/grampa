{-# LANGUAGE FlexibleContexts, KindSignatures, RankNTypes, RecordWildCards, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Classes
   MonoidNull, FactorialMonoid, LeftReductiveMonoid, TextualMonoid, MonoidParsing,
   -- * Types
   Grammar, GrammarBuilder, Analysis, Parser, ParseResults,
   -- * Grammar and parser manipulation
   fixGrammar, fixGrammarAnalysis, parsePrefix, parseAll, simpleParse, nullableRecursive,
   -- * Parser combinators
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead,
   (<<|>),
   leftRecursive,
   -- * Parsing primitives
   endOfInput, getInput, anyToken, token, satisfy, satisfyChar, string,
   scan, scanChars, takeWhile, takeWhile1, takeCharsWhile, takeCharsWhile1, whiteSpace)
where

import Control.Applicative
import Control.Arrow((&&&))
import Control.Monad.Trans.State.Lazy (State, evalState, get, put)

import Data.Maybe (maybe)
import Data.Monoid (All(..), Any(..), (<>))
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet

import Data.Monoid.Cancellative (LeftReductiveMonoid)
import Data.Monoid.Null (MonoidNull)
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)

import qualified Data.Monoid.Factorial as Factorial

import Text.Parser.Char (CharParsing(char, notChar, anyChar))
import Text.Parser.Combinators (Parsing((<?>), notFollowedBy, skipMany, skipSome, unexpected))
import Text.Parser.LookAhead (LookAheadParsing(lookAhead))

import qualified Rank2
import Text.Grampa.Parser (Parser(applyParser), ParseResults, ResultList(..))
import Text.Grampa.Analysis (Analysis(..), leftRecursive)
import qualified Text.Grampa.Parser as Parser
import qualified Text.Grampa.Analysis as Analysis

import Prelude hiding (takeWhile)

type Grammar (g  :: (* -> *) -> *) p s = g (p g s)
type GrammarBuilder (g  :: (* -> *) -> *)
                    (g' :: (* -> *) -> *)
                    (p  :: ((* -> *) -> *) -> * -> * -> *)
                    (s  :: *)
   = g (p g' s) -> g (p g' s)

class MonoidParsing (m :: * -> * -> *) where
   infixl 3 <<|>
   (<<|>) :: m s r -> m s r -> m s r
   endOfInput :: MonoidNull s => m s ()
   getInput :: Monoid s => m s s
   anyToken :: FactorialMonoid s => m s s
   token :: (Eq s, FactorialMonoid s) => s -> m s s
   satisfy :: FactorialMonoid s => (s -> Bool) -> m s s
   satisfyChar :: TextualMonoid s => (Char -> Bool) -> m s Char
   scan :: FactorialMonoid t => s -> (s -> t -> Maybe s) -> m t t
   scanChars :: TextualMonoid t => s -> (s -> Char -> Maybe s) -> m t t
   string :: (FactorialMonoid s, LeftReductiveMonoid s, Show s) => s -> m s s
   takeWhile :: FactorialMonoid s => (s -> Bool) -> m s s
   takeWhile1 :: FactorialMonoid s => (s -> Bool) -> m s s
   takeCharsWhile :: TextualMonoid s => (Char -> Bool) -> m s s
   takeCharsWhile1 :: TextualMonoid s => (Char -> Bool) -> m s s
   whiteSpace :: TextualMonoid s => m s ()

instance MonoidParsing (Parser g) where
   (<<|>) = (Parser.<<|>)
   endOfInput = Parser.endOfInput
   getInput = Parser.getInput
   anyToken = Parser.anyToken
   token = Parser.token
   satisfy = Parser.satisfy
   satisfyChar = Parser.satisfyChar
   scan = Parser.scan
   scanChars = Parser.scanChars
   string = Parser.string
   takeWhile = Parser.takeWhile
   takeWhile1 = Parser.takeWhile1
   takeCharsWhile = Parser.takeCharsWhile
   takeCharsWhile1 = Parser.takeCharsWhile1
   whiteSpace = Parser.whiteSpace

instance MonoidParsing (Analysis g) where
   (<<|>) = (Analysis.<<|>)
   endOfInput = Analysis.endOfInput
   getInput = Analysis.getInput
   anyToken = Analysis.anyToken
   token = Analysis.token
   satisfy = Analysis.satisfy
   satisfyChar = Analysis.satisfyChar
   scan = Analysis.scan
   scanChars = Analysis.scanChars
   string = Analysis.string
   takeWhile = Analysis.takeWhile
   takeWhile1 = Analysis.takeWhile1
   takeCharsWhile = Analysis.takeCharsWhile
   takeCharsWhile1 = Analysis.takeCharsWhile1
   whiteSpace = Analysis.whiteSpace

parsePrefix :: (Rank2.Apply g, Rank2.Foldable g, FactorialMonoid s) =>
               g (Analysis g s) -> (forall f. g f -> f r) -> s -> ParseResults (r, s)
parsePrefix g prod input = Parser.fromResultList input (prod $ snd $ head $ parseRecursive g input)

parseAll :: (FactorialMonoid s, Rank2.Traversable g, Rank2.Distributive g, Rank2.Apply g) =>
            g (Analysis g s) -> (forall f. g f -> f r) -> s -> ParseResults r
parseAll g prod input = (fst <$>) <$>
                        Parser.fromResultList input (prod $ snd $ head $ reparse close $ parseRecursive g input)
   where close = Rank2.fmap (<* endOfInput) selfReferring

simpleParse :: FactorialMonoid s => Parser (Rank2.Singleton r) s r -> s -> ParseResults (r, s)
simpleParse p input =
   Parser.fromResultList input (Rank2.getSingle $ snd $ head $ parseNonRecursive (Rank2.Singleton p) input)

reparse :: Rank2.Functor g => g (Parser g s) -> [(s, g (ResultList g s))] -> [(s, g (ResultList g s))]
reparse _ [] = []
reparse final parsed@((s, _):_) = (s, gd):parsed
   where gd = Rank2.fmap (`applyParser` parsed) final

parseRecursive :: (Rank2.Apply g, Rank2.Foldable g, FactorialMonoid s) => 
                  g (Analysis g s) -> s -> [(s, g (ResultList g s))]
parseRecursive analysis = parseSeparated
                             (Rank2.fmap (Const . leftDescendants) analysis)
                             (Rank2.fmap recursive analysis)
                             (Rank2.fmap Analysis.direct analysis)

parseNonRecursive :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> [(s, g (ResultList g s))]
parseNonRecursive g input = foldr parseTail [] (Factorial.tails input) where
  parseTail s parsedTail = parsed where
    parsed = (s,d):parsedTail
    d      = Rank2.fmap (($ parsed) . applyParser) g

parseSeparated :: (Rank2.Apply g, Rank2.Foldable g, FactorialMonoid s) =>
                  g (Const (g (Const Bool))) -> g (Parser g s) -> g (Parser g s) -> s -> [(s, g (ResultList g s))]
parseSeparated dependencies recursive direct input = foldr parseTail [] (Factorial.tails input) where
   parseTail s parsedTail = parsed where
      parsed = (s,d'):parsedTail
      d      = Rank2.fmap (($ (s,d):parsedTail) . applyParser) direct
      d'     = fixRecursive dependencies recursive s parsedTail d

-- | Produce a 'Grammar' from its recursive definition
fixGrammar :: Rank2.Distributive g => (g (Parser g i) -> g (Parser g i)) -> g (Parser g i)
fixGrammar gf = gf selfReferring

selfReferring :: Rank2.Distributive g => g (Parser g i)
selfReferring = Rank2.distributeWith nt id

nt :: (g (ResultList g i) -> ResultList g i a) -> Parser g i a
nt f = Parser.Parser p where
   p ((_, d) : _) = f d
   p _ = NoParse (Parser.FailureInfo 1 0 ["NonTerminal at endOfInput"])

nullableRecursive :: Analysis g i a -> Analysis g i a
nullableRecursive a = a{nullable= True,
                        recursivelyNullable= const True}

fixGrammarAnalysis :: forall g i. (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g) =>
                      (g (Analysis g i) -> g (Analysis g i)) -> g (Analysis g i)
fixGrammarAnalysis gf = Rank2.fmap collapsed (cycled $ ordered $ fixNullable $ gf $
                                              Rank2.liftA2 setRecursive selfReferring selfAnalysis)
   where selfAnalysis = Rank2.distributeWith separated id
         setRecursive :: Parser g i a -> Analysis g i a -> Analysis g i a
         setRecursive p a = a{recursive= p}
         orderedNullable = ordered (fixNullable $ gf selfNullable)
         ordered :: g (Analysis g i) -> g (Analysis g i)
         ordered g = evalState (Rank2.traverse f g) 0
            where f :: Analysis g i a -> State Int (Analysis g i a)
                  f a = do {n <- get; put (n+1); return a{index= Just n}}
         separated :: (g (Analysis g i) -> Analysis g i a) -> Analysis g i a
         separated f = an{nullDirect = empty,
                          positiveDirect = empty,
                          recursive= error "recursive is still undefined",
                          leftRecursiveOn= maybe [] (:[]) (index $ f orderedNullable)}
            where an = f orderedNullable
         collapsed a
            | hasCycle a = a
            | otherwise = a{nullDirect= nullDirect a <|> recursive a,
                            recursive= empty}
         cycled :: g (Analysis g i) -> g (Analysis g i)
         cycled g = evalState (Rank2.traverse addDepth g) $
                    IntMap.elems $ calcLeftSets $ IntMap.fromList $ zip [0..] $ Rank2.foldMap successorSet g
         addDepth :: Analysis g i a -> State [(Bool, IntSet)] (Analysis g i a)
         addDepth a = do (cyclic, descendants):rest <- get
                         put rest
                         return a{hasCycle= cyclic,
                                  leftDescendants= setToBools descendants}
         setToBools :: IntSet -> g (Const Bool)
         setToBools = Rank2.traverse isElem orderedNullable
         isElem :: Analysis g i a -> IntSet -> Const Bool a
         isElem Analysis{index= Just i} s = Const (IntSet.member i s)
         successorSet :: Analysis g i a -> [IntSet]
         successorSet a = [IntSet.fromList $ leftRecursiveOn a]

data AdvanceFront = AdvanceFront{visited       :: IntSet,
                                 cyclic        :: Bool,
                                 front         :: IntSet}
                  deriving Show

calcLeftSets :: IntMap IntSet -> IntMap (Bool, IntSet)
calcLeftSets successors = (cyclic &&& visited) <$> expandPaths initialDepths
   where expandPaths :: IntMap AdvanceFront -> IntMap AdvanceFront
         expandPaths paths
            | all (IntSet.null . front) paths' = paths'
            | otherwise = expandPaths paths'
            where paths' = expandReachables <$> paths
                  expandReachables :: AdvanceFront -> AdvanceFront
                  expandReachables AdvanceFront{..} = 
                     AdvanceFront{visited= visited <> front,
                                  cyclic= cyclic || not (IntSet.null $ IntSet.intersection front visited),
                                  front= IntSet.foldr' advance mempty (IntSet.difference front visited)}
         advance :: Int -> IntSet -> IntSet
         advance node front = front <> successors IntMap.! node
         initialDepths = IntMap.mapWithKey setToFront successors
         setToFront root set = AdvanceFront{visited= mempty,
                                            cyclic= IntSet.member root set,
                                            front= set}

selfNullable :: forall g i. Rank2.Distributive g => g (Analysis g i)
selfNullable = Rank2.distributeWith nonTerminal id
   where nonTerminal :: forall a. (g (Analysis g i) -> Analysis g i a) -> Analysis g i a
         nonTerminal f = Analysis{index= error "direct is still undefined",
                                  nullDirect = error "direct is still undefined",
                                  positiveDirect = error "direct is still undefined",
                                  recursive= error "recursive is still undefined",
                                  leftRecursiveOn= error "leftRecursiveOn is still undefined",
                                  leftDescendants= error "undefined leftDescendants",
                                  nullable= True,
                                  recursivelyNullable= nullable . f}

fixNullable :: (Rank2.Apply g, Rank2.Foldable g) => g (Analysis g i) -> g (Analysis g i)
fixNullable g
   | getAll (Rank2.foldMap (All . getConst) $ Rank2.liftA2 equallyNullable g g') = g
   | otherwise = fixNullable g'
   where g' = Rank2.fmap recurseNullable g
         recurseNullable a = a{nullable= nullable a && recursivelyNullable a g}
         equallyNullable a1 a2 = Const $ nullable a1 == nullable a2

newtype CountedResult g i a = CountedResult (Int -> Maybe (ResultList g i a))

fixRecursive :: forall g i. (Rank2.Apply g, Rank2.Foldable g) =>
                g (Const (g (Const Bool))) -> g (Parser g i) -> i -> [(i, g (ResultList g i))] -> g (ResultList g i)
             -> g (ResultList g i)
fixRecursive dependencies recursive s parsedTail initial =
   foldr1 (whileAnyContinues dependencies) $ 
   iterate (recurseOnce s parsedTail recursive) initial

whileAnyContinues :: forall g i. (Rank2.Apply g, Rank2.Foldable g) => 
                     g (Const (g (Const Bool))) -> g (ResultList g i) -> g (ResultList g i) -> g (ResultList g i)
whileAnyContinues dependencies g1 g2 = Rank2.liftA3 choiceWhile dependencies g1 g2
   where choiceWhile :: Const (g (Const Bool)) x -> ResultList g i x -> ResultList g i x -> ResultList g i x
         combine :: Const Bool x -> ResultList g i x -> Const Bool x
         choiceWhile (Const deps) r1 r2
            | getAny (Rank2.foldMap (Any . getConst) (Rank2.liftA2 combine deps g1)) = r1 <> r2
            | otherwise = r1
         combine (Const False) _ = Const False
         combine (Const True) (Parsed (_:_)) = Const True
         combine (Const True) _ = Const False

addCount :: ResultList g i a -> CountedResult g i a
addCount r = CountedResult (const $ Just r)

dropCount :: Int -> CountedResult g i a -> ResultList g i a
dropCount limit (CountedResult f) = case f limit
                                    of Nothing -> NoParse (Parser.FailureInfo 1 maxBound ["dropCount"])
                                       Just r -> r

countedChoice :: Rank2.Apply g =>
                 g (Const Int) -> g (CountedResult g i) -> g (CountedResult g i) -> g (CountedResult g i)
countedChoice limits g1 g2 = Rank2.liftA3 (choiceTill . getConst) limits g1 g2
   where choiceTill limit (CountedResult cr1) (CountedResult cr2) = CountedResult cr'
            where cr' 0 = Nothing
                  cr' n = case cr1 n
                          of Nothing -> Nothing
                             Just NoParse{} -> cr2 (pred n)
                             r -> r <> cr2 limit

recurseOnce :: Rank2.Apply g =>
               i -> [(i, g (ResultList g i))] -> g (Parser g i) -> g (ResultList g i) -> g (ResultList g i)
recurseOnce s parsedTail recursive initial = Rank2.fmap (($ parsed). applyParser) recursive
   where parsed = (s, initial):parsedTail
