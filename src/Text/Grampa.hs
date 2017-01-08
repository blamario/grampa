{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa (
   -- * Classes
   MonoidNull, FactorialMonoid, TextualMonoid,
   -- * Types
   Grammar, GrammarBuilder, Parser, ParseResults,
   -- * Grammar and parser manipulation
   fixGrammar, fixGrammarInput, parse, parseAll, simpleParse,
   -- * Parser combinators
   module Text.Parser.Char,
   module Text.Parser.Combinators,
   module Text.Parser.LookAhead,
   module Text.Parser.Token,
   recursiveOn, (<<|>),
   -- * Parsing primitives
   endOfInput, getInput, anyToken, token, satisfy, satisfyChar, spaces, string,
   scan, scanChars, takeWhile, takeWhile1, takeCharsWhile, takeCharsWhile1, skipCharsWhile)
where

import Control.Applicative
import Data.Char (isSpace)
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid(mempty), All(..), (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(length, spanMaybe', splitPrimePrefix, tails))
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual

import Text.Parser.Char (CharParsing(char, notChar, anyChar))
import Text.Parser.Combinators (Parsing((<?>), notFollowedBy, skipMany, skipSome, unexpected))
import Text.Parser.LookAhead (LookAheadParsing(lookAhead))
import Text.Parser.Token (whiteSpace)

import qualified Rank2
import Text.Grampa.Types

import Prelude hiding (iterate, length, null, span, takeWhile)

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
fixNullable g = head (iterateNullable iter g [])
   where iter g' = Rank2.fmap (iterP g') g'
         iterP g' p = p{nullable= recursivelyNullable p g'}

iterateNullable :: forall g s. (Rank2.Foldable g, Rank2.Apply g) =>
                   (g (Parser g s) -> g (Parser g s)) -> g (Parser g s)
                -> [g (Parser g s)]
                -> [g (Parser g s)]
iterateNullable f n ns = if getAll (Rank2.foldMap (All . getConst) $ equallyNullable `Rank2.fmap` n `Rank2.ap` n')
                         then n':n:ns else iterateNullable f n' (n:ns)
   where n' = f n
         equallyNullable :: forall x. Parser g s x -> Rank2.Arrow (Parser g s) (Const Bool) x
         equallyNullable p1 = Rank2.Arrow (\p2-> Const $ nullable p1 == nullable p2)

selfNullable :: forall g s. Rank2.Distributive g => Grammar g s
selfNullable = Rank2.distributeWith nonTerminal id
   where nonTerminal :: forall r. (g (Parser g s) -> Parser g s r) -> Parser g s r
         nonTerminal f = Parser{continued= undefined,
                                direct= undefined,
                                recursive= undefined,
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
                 then n':n:ns else iterate f n' (n:ns)
   where n' = f n

recursiveOn :: Parser g s x -> Parser g s r -> Parser g s r
recursiveOn p q = q{nullable= nullable p,
                    recursivelyNullable= recursivelyNullable p,
                    recursive= recursive p *> recursive q}

spaces :: (TextualMonoid t) => Parser g t ()
spaces = skipCharsWhile isSpace

-- | Always sucessful parser that returns the remaining input without consuming it.
getInput :: (MonoidNull s) => Parser g s s
getInput = primitive True f
   where f s t rc0 rc _fc
            | null s = rc0 s
            | otherwise = rc s [last t]

-- | A parser accepting the longest sequence of input atoms that match the given predicate; an optimized version of
-- 'concatMany . satisfy'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeWhile :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
takeWhile predicate = primitive True f
   where f s t rc0 rc _fc = if null prefix then rc0 prefix else rc prefix (drop (length prefix - 1) t)
            where prefix = Factorial.takeWhile predicate s

-- | A parser accepting the longest non-empty sequence of input atoms that match the given predicate; an optimized
-- version of 'concatSome . satisfy'.
takeWhile1 :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
takeWhile1 predicate = primitive False f
   where f s t _rc0 rc fc
            | null prefix = fc "takeCharsWhile1"
            | otherwise = rc prefix (drop (length prefix - 1) t)
            where prefix = Factorial.takeWhile predicate s

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
takeCharsWhile :: (TextualMonoid s) => (Char -> Bool) -> Parser g s s
takeCharsWhile predicate = primitive True f
   where f s t rc0 rc _fc = if null prefix then rc0 prefix else rc prefix (drop (length prefix - 1) t)
            where prefix = Textual.takeWhile_ False predicate s

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
takeCharsWhile1 :: (TextualMonoid s) => (Char -> Bool) -> Parser g s s
takeCharsWhile1 predicate = primitive False f
   where f s t _rc0 rc fc
            | null prefix = fc "takeCharsWhile1"
            | otherwise = rc prefix (drop (length prefix - 1) t)
            where prefix = Textual.takeWhile_ False predicate s

-- | A stateful scanner.  The predicate consumes and transforms a state argument, and each transformed state is passed
-- to successive invocations of the predicate on each token of the input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first prime
-- input factor.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scan :: (FactorialMonoid t) => s -> (s -> t -> Maybe s) -> Parser g t t
scan s0 f = primitive True (go s0)
 where go s i t rc0 rc _fc = if null prefix then rc0 prefix else rc prefix (drop (length prefix - 1) t)
          where (prefix, _, _) = spanMaybe' s f i

-- | A stateful scanner.  The predicate consumes and transforms a
-- state argument, and each transformed state is passed to successive invocations of the predicate on each token of the
-- input until one returns 'Nothing' or the input ends.
--
-- This parser does not fail.  It will return an empty string if the predicate returns 'Nothing' on the first character.
--
-- /Note/: Because this parser does not fail, do not use it with combinators such as 'many', because such parsers loop
-- until a failure occurs.  Careless use will thus result in an infinite loop.
scanChars :: (TextualMonoid t) => s -> (s -> Char -> Maybe s) -> Parser g t t
scanChars s0 f = primitive True (go s0)
 where go s i t rc0 rc _fc = if null prefix then rc0 prefix else rc prefix (drop (length prefix - 1) t)
          where (prefix, _, _) = Textual.spanMaybe_' s f i

-- | A parser that accepts any single input atom.
anyToken :: (FactorialMonoid s) => Parser g s s
anyToken = primitive False f
   where f s t _rc0 rc fc =
            case splitPrimePrefix s
            of Just (first, _) -> rc first t
               _ -> fc "anyToken"

-- | A parser that accepts a specific input atom.
token :: (Eq s, FactorialMonoid s) => s -> Parser g s s
token x = satisfy (== x)

-- | A parser that accepts an input atom only if it satisfies the given predicate.
satisfy :: (FactorialMonoid s) => (s -> Bool) -> Parser g s s
satisfy predicate = primitive False f
   where f s t _rc0 rc fc =
            case splitPrimePrefix s
            of Just (first, _) | predicate first -> rc first t
               _ -> fc "satisfy"

-- | Specialization of 'takeWhile' on 'TextualMonoid' inputs, accepting the longest sequence of input characters that
-- match the given predicate; an optimized version of 'concatMany . satisfyChar'.
skipCharsWhile :: (TextualMonoid s) => (Char -> Bool) -> Parser g s ()
skipCharsWhile predicate = primitive True f
   where f s t rc0 rc _fc = if null prefix then rc0 () else rc () (drop (length prefix - 1) t)
            where prefix = Textual.takeWhile_ False predicate s
