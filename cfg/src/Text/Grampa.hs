{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Classes
   MonoidNull, FactorialMonoid, LeftReductiveMonoid, TextualMonoid,
   -- * Types
   Grammar, GrammarBuilder, Parser, ParseResults,
   -- * Grammar and parser manipulation
   fixGrammar, fixGrammarInput, parse, parseAll, simpleParse,
   -- * Parser combinators
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead,
   recursiveOn, (<<|>),
   -- * Parsing primitives
   endOfInput, getInput, anyToken, token, satisfy, satisfyChar, string,
   scan, scanChars, takeWhile, takeWhile1, takeCharsWhile, takeCharsWhile1, whiteSpace)
where

import Control.Applicative
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid(mempty), All(..), (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid)
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(length, tails))
import Data.Monoid.Textual (TextualMonoid)

import Text.Parser.Char (CharParsing(char, notChar, anyChar))
import Text.Parser.Combinators (Parsing((<?>), notFollowedBy, skipMany, skipSome, unexpected))
import Text.Parser.LookAhead (LookAheadParsing(lookAhead))

import qualified Rank2
import Text.Grampa.Types

import Prelude hiding (iterate, length, null, takeWhile)

type GrammarBuilder g g' s = g (Parser g' s) -> g (Parser g' s)
type ParseResults r = Either (Int, [String]) [r]

newtype DerivedResultList g s r = DerivedResultList {
   derivedResultList :: g (ResultList g s) -> ResultList g s r}

instance Functor (DerivedResultList g s) where
   fmap f (DerivedResultList gd) = DerivedResultList ((f <$>) <$> gd)

parse :: (FactorialMonoid s, Rank2.Traversable g, Rank2.Distributive g, Rank2.Apply g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults (r, s)
parse g prod input = fromResultList input (prod $ fst $ head $ fixGrammarInput selfReferring g input)

parseAll :: (FactorialMonoid s, Rank2.Traversable g, Rank2.Distributive g, Rank2.Apply g) =>
         Grammar g s -> (forall f. g f -> f r) -> s -> ParseResults r
parseAll g prod input = (fst <$>) <$> fromResultList input (prod $ fst $ head $ fixGrammarInput close g input)
   where close = Rank2.fmap (<* endOfInput) selfReferring

simpleParse :: FactorialMonoid s => Parser (Rank2.Singleton r) s r -> s -> ParseResults (r, s)
simpleParse p = parse (Rank2.Singleton p) Rank2.getSingle

fromResultList :: FactorialMonoid s => s -> ResultList g s r -> ParseResults (r, s)
fromResultList s (ResultList (Left (FailureInfo _ pos msgs))) = Left (length s - fromIntegral pos, nub msgs)
fromResultList input (ResultList (Right rl)) = Right (f <$> rl)
   where f (CompleteResultInfo ((_, s):_) r) = (r, s)
         f (CompleteResultInfo [] r) = (r, mempty)
         f (StuckResultInfo r) = (r, input)


-- | Tie the knot on a 'GrammarBuilder' and turn it into a 'Grammar'
fixGrammar :: forall g s. (Rank2.Foldable g, Rank2.Apply g, Rank2.Distributive g) =>
              (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar gf = (Rank2.Arrow . combine) `Rank2.fmap` gf selfReferring `Rank2.ap` fixNullable (gf selfNullable)
   where combine p1 p2 = Parser{continued= continued p1,
                                direct= direct p1,
                                recursive= recursive p1,
                                nullable= nullable p2,
                                recursivelyNullable= recursivelyNullable p2}

fixNullable :: forall g s. (Rank2.Foldable g, Rank2.Apply g) => Grammar g s -> Grammar g s
fixNullable g = Rank2.fmap (iterP $ iterateNullable iter g) g
   where iter g' = Rank2.fmap (iterP g') g'
         iterP g' p = p{nullable= nullable p && recursivelyNullable p g'}

iterateNullable :: forall g s. (Rank2.Foldable g, Rank2.Apply g) =>
                   (g (Parser g s) -> g (Parser g s)) -> g (Parser g s)
                -> g (Parser g s)
iterateNullable f n = if getAll (Rank2.foldMap (All . getConst) $ equallyNullable `Rank2.fmap` n `Rank2.ap` n')
                      then n' else iterateNullable f n'
   where n' = f n
         equallyNullable :: forall x. Parser g s x -> Rank2.Arrow (Parser g s) (Const Bool) x
         equallyNullable p1 = Rank2.Arrow (\p2-> Const $ nullable p1 == nullable p2)

selfNullable :: forall g s. Rank2.Distributive g => Grammar g s
selfNullable = Rank2.distributeWith nonTerminal id
   where nonTerminal :: forall r. (g (Parser g s) -> Parser g s r) -> Parser g s r
         nonTerminal f = Parser{continued= undefined,
                                direct= undefined,
                                recursive= Just undefined,
                                nullable= True,
                                recursivelyNullable= nullable . f}

selfReferring :: forall g s. Rank2.Distributive g => Grammar g s
selfReferring = Rank2.distributeWith nonTerminal id
   where nonTerminal :: forall r. (g (ResultList g s) -> ResultList g s r) -> Parser g s r
         nonTerminal f = Parser{continued= continue . resultList . f . fst . head,
                                direct= mempty,
                                recursive= Just (const . const . f),
                                nullable= True,
                                recursivelyNullable= error "recursivelyNullable will be initialized by selfNullable"}
            where continue :: Either FailureInfo [ResultInfo g s r]
                           -> (r -> [(GrammarResults g s, s)] -> ResultList g s r')
                           -> (FailureInfo -> ResultList g s r')
                           -> ResultList g s r'
                  continue (Left (FailureInfo strength pos msgs)) _ fc = fc (FailureInfo (succ strength) pos msgs)
                  continue (Right rs) rc _ = foldMap continueFrom rs
                     where continueFrom (CompleteResultInfo t r) = rc r t
                           continueFrom StuckResultInfo{} = error "Can't continue, I'm Stuck."

fixGrammarInput :: forall s g. (FactorialMonoid s, Rank2.Apply g, Rank2.Traversable g) =>
                   Grammar g s -> Grammar g s -> s -> [(GrammarResults g s, s)]
fixGrammarInput final grammar input = parseTailWith input $ foldr parseTail [] (tails input)
   where parseTail :: s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTail s parsedTail = parsed
            where parsed = (Rank2.fmap finalize $ collectGrammarResults gd gr, s):parsedTail
                  gd = Rank2.fmap (\p-> direct p s parsedTail) grammar
                  gr = Rank2.fmap (\p-> DerivedResultList $ \g-> fromMaybe mempty (recursive p) g s parsedTail) grammar
                  finalize :: ResultList g s r -> ResultList g s r
                  finalize (ResultList (Left err)) = ResultList (Left err)
                  finalize (ResultList (Right results)) = ResultList (Right $ complete <$> results)
                  complete :: ResultInfo g s r -> ResultInfo g s r
                  complete r@CompleteResultInfo{} = r
                  complete (StuckResultInfo r) = CompleteResultInfo parsed r
         parseTailWith :: s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTailWith s parsed = (gd, s):parsed
            where gd = Rank2.fmap (\p-> continued p parsed succeed concede) final

collectGrammarResults :: (Rank2.Apply g, Rank2.Traversable g) =>
                         g (ResultList g s) -> g (DerivedResultList g s) -> g (ResultList g s)
collectGrammarResults gd gdr = foldr1 (Rank2.liftA2 (<>)) (iterate rf gd [])
   where rf = Rank2.traverse derivedResultList gdr

iterate :: Rank2.Foldable g =>
           (g (ResultList g s) -> g (ResultList g s)) -> g (ResultList g s)
        -> [g (ResultList g s)]
        -> [g (ResultList g s)]
iterate f n ns = if getAll (Rank2.foldMap (either (const mempty) (All . null) . resultList) n')
                 then n:ns else iterate f n' (n:ns)
   where n' = f n

recursiveOn :: Parser g s x -> Parser g s r -> Parser g s r
recursiveOn p q = q{nullable= nullable p,
                    recursivelyNullable= recursivelyNullable p,
                    recursive= recursive p *> recursive q}
