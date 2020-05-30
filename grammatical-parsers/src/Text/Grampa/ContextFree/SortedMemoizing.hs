{-# LANGUAGE BangPatterns, FlexibleContexts, GeneralizedNewtypeDeriving, InstanceSigs,
             RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Text.Grampa.ContextFree.SortedMemoizing 
       (FailureInfo(..), ResultList(..), Parser(..),
        longest, peg, terminalPEG)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
import Data.Functor.Compose (Compose(..))
import Data.List (genericLength)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Monoid (Monoid(mappend, mempty))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid, splitPrimePrefix)
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.Semigroup (Semigroup((<>)))
import Data.Semigroup.Cancellative (LeftReductive(isPrefixOf))
import Data.String (fromString)

import qualified Text.Parser.Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))

import qualified Rank2

import Text.Grampa.Class (GrammarParsing(..), InputParsing(..), InputCharParsing(..), MultiParsing(..),
                          AmbiguousParsing(..), Ambiguous(Ambiguous),
                          ConsumedInputParsing(..), DeterministicParsing(..),
                          TailsParsing(parseTails, parseAllTails), ParseResults, Expected(..))
import Text.Grampa.Internal (FailureInfo(..), ResultList(..), ResultsOfLength(..), fromResultList)
import qualified Text.Grampa.PEG.Backtrack.Measured as Backtrack

import Prelude hiding (iterate, length, null, showList, span, takeWhile)

-- | Parser for a context-free grammar with packrat-like sharing of parse results. It does not support left-recursive
-- grammars.
newtype Parser g s r = Parser{applyParser :: [(s, g (ResultList g s))] -> ResultList g s r}

instance Functor (Parser g i) where
   fmap f (Parser p) = Parser (fmap f . p)
   {-# INLINE fmap #-}

instance Applicative (Parser g i) where
   pure a = Parser (\rest-> ResultList [ResultsOfLength 0 rest (a:|[])] mempty)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultsOfLength l rest' fs) = foldMap (continue' l $ q rest') fs
      continue' l (ResultList rs failure) f = ResultList (adjust l f <$> rs) failure
      adjust l f (ResultsOfLength l' rest' as) = ResultsOfLength (l+l') rest' (f <$> as)
   {-# INLINABLE pure #-}
   {-# INLINABLE (<*>) #-}

instance Alternative (Parser g i) where
   empty = Parser (\rest-> ResultList mempty $ FailureInfo (genericLength rest) [])
   Parser p <|> Parser q = Parser r where
      r rest = p rest <> q rest
   {-# INLINE (<|>) #-}
   {-# INLINABLE empty #-}

instance Monad (Parser g i) where
   return = pure
   (>>) = (*>)
   Parser p >>= f = Parser q where
      q rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultsOfLength l rest' rs) = foldMap (continue' l . flip applyParser rest' . f) rs
      continue' l (ResultList rs failure) = ResultList (adjust l <$> rs) failure
      adjust l (ResultsOfLength l' rest' rs) = ResultsOfLength (l+l') rest' rs

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Semigroup x => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance (Eq s, LeftReductive s, FactorialMonoid s) => GrammarParsing (Parser g s) where
   type ParserGrammar (Parser g s) = g
   type GrammarFunctor (Parser g s) = ResultList g s
   parsingResult s = Compose . fromResultList s
   nonTerminal :: (Rank2.Functor g, ParserInput (Parser g s) ~ s) => (g (ResultList g s) -> ResultList g s a) -> Parser g s a
   nonTerminal f = Parser p where
      p ((_, d) : _) = f d
      p _ = ResultList mempty (FailureInfo 0 [Expected "NonTerminal at endOfInput"])
   {-# INLINE nonTerminal #-}

instance (Eq s, LeftReductive s, FactorialMonoid s) => TailsParsing (Parser g s) where
   parseTails = applyParser

-- | Memoizing parser guarantees O(n²) performance for grammars with unambiguous productions, but provides no left
-- recursion support.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Memoizing.'Parser' g s) -> s -> g ('Compose' ('ParseResults' s) [])
-- @
instance (LeftReductive s, FactorialMonoid s) => MultiParsing (Parser g s) where
   type GrammarConstraint (Parser g s) g' = (g ~ g', Rank2.Functor g)
   type ResultFunctor (Parser g s) = Compose (ParseResults s) []
   -- | Returns the list of all possible input prefix parses paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . Compose . fromResultList input) (snd $ head $ parseGrammarTails g input)
   parseComplete :: (ParserInput (Parser g s) ~ s, Rank2.Functor g, Eq s, FactorialMonoid s) =>
                    g (Parser g s) -> s -> g (Compose (ParseResults s) [])
   parseComplete g input = Rank2.fmap ((snd <$>) . Compose . fromResultList input)
                              (snd $ head $ parseAllTails close $ parseGrammarTails g input)
      where close = Rank2.fmap (<* eof) g

parseGrammarTails :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> [(s, g (ResultList g s))]
parseGrammarTails g input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d):parsedTail
                  d      = Rank2.fmap (($ parsed) . applyParser) g

instance (LeftReductive s, FactorialMonoid s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   endOfInput = eof
   getInput = Parser p
      where p rest@((s, _):_) = ResultList [ResultsOfLength 0 rest (s:|[])] mempty
            p [] = ResultList [ResultsOfLength 0 [] (mempty:|[])] mempty
   anyToken = Parser p
      where p rest@((s, _):t) = case splitPrimePrefix s
                                of Just (first, _) -> ResultList [ResultsOfLength 1 t (first:|[])] mempty
                                   _ -> ResultList mempty (FailureInfo (genericLength rest) [Expected "anyToken"])
            p [] = ResultList mempty (FailureInfo 0 [Expected "anyToken"])
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case splitPrimePrefix s
               of Just (first, _) | predicate first -> ResultList [ResultsOfLength 1 t (first:|[])] mempty
                  _ -> ResultList mempty (FailureInfo (genericLength rest) [Expected "satisfy"])
            p [] = ResultList mempty (FailureInfo 0 [Expected "satisfy"])
   scan s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = ResultList [ResultsOfLength l (drop l rest) (prefix:|[])] mempty
               where (prefix, _, _) = Factorial.spanMaybe' s f i
                     l = Factorial.length prefix
            p _ [] = ResultList [ResultsOfLength 0 [] (mempty:|[])] mempty
   takeWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, l <- Factorial.length x =
                    ResultList [ResultsOfLength l (drop l rest) (x:|[])] mempty
            p [] = ResultList [ResultsOfLength 0 [] (mempty:|[])] mempty
   takeWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, l <- Factorial.length x, l > 0 =
                    ResultList [ResultsOfLength l (drop l rest) (x:|[])] mempty
            p rest = ResultList mempty (FailureInfo (genericLength rest) [Expected "takeWhile1"])
   string s = Parser p where
      p rest@((s', _) : _)
         | s `isPrefixOf` s' = ResultList [ResultsOfLength l (Factorial.drop l rest) (s:|[])] mempty
      p rest = ResultList mempty (FailureInfo (genericLength rest) [ExpectedInput s])
      l = Factorial.length s
   notSatisfy predicate = Parser p
      where p rest@((s, _):_)
               | Just (first, _) <- splitPrimePrefix s, 
                 predicate first = ResultList mempty (FailureInfo (genericLength rest) [Expected "notSatisfy"])
            p rest = ResultList [ResultsOfLength 0 rest (():|[])] mempty
   {-# INLINABLE string #-}

instance (Show s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyCharInput predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> ResultList [ResultsOfLength 1 t (Factorial.primePrefix s:|[])] mempty
                  _ -> ResultList mempty (FailureInfo (genericLength rest) [Expected "satisfyCharInput"])
            p [] = ResultList mempty (FailureInfo 0 [Expected "satisfyCharInput"])
   scanChars s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = ResultList [ResultsOfLength l (drop l rest) (prefix:|[])] mempty
               where (prefix, _, _) = Textual.spanMaybe_' s f i
                     l = Factorial.length prefix
            p _ [] = ResultList [ResultsOfLength 0 [] (mempty:|[])] mempty
   takeCharsWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, l <- Factorial.length x =
                    ResultList [ResultsOfLength l (drop l rest) (x:|[])] mempty
            p [] = ResultList [ResultsOfLength 0 [] (mempty:|[])] mempty
   takeCharsWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, l <- Factorial.length x, l > 0 =
                    ResultList [ResultsOfLength l (drop l rest) (x:|[])] mempty
            p rest = ResultList mempty (FailureInfo (genericLength rest) [Expected "takeCharsWhile1"])
   notSatisfyChar predicate = Parser p
      where p rest@((s, _):_)
               | Just first <- Textual.characterPrefix s, 
                 predicate first = ResultList mempty (FailureInfo (genericLength rest) [Expected "notSatisfyChar"])
            p rest = ResultList [ResultsOfLength 0 rest (():|[])] mempty

instance (LeftReductive s, FactorialMonoid s) => ConsumedInputParsing (Parser g s) where
   match (Parser p) = Parser q
      where q [] = addConsumed mempty (p [])
            q rest@((s, _) : _) = addConsumed s (p rest)
            addConsumed input (ResultList rl failure) = ResultList (add1 <$> rl) failure
               where add1 (ResultsOfLength l t rs) = ResultsOfLength l t ((,) (Factorial.take l input) <$> rs)

instance MonoidNull s => Parsing (Parser g s) where
   try (Parser p) = Parser q
      where q rest = rewindFailure (p rest)
               where rewindFailure (ResultList rl (FailureInfo _pos _msgs)) =
                        ResultList rl (FailureInfo (genericLength rest) [])
   Parser p <?> msg  = Parser q
      where q rest = replaceFailure (p rest)
               where replaceFailure (ResultList [] (FailureInfo pos msgs)) =
                        ResultList [] (FailureInfo pos $ if pos == genericLength rest then [Expected msg] else msgs)
                     replaceFailure rl = rl
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList [] _) = ResultList [ResultsOfLength 0 t (():|[])] mempty
            rewind t ResultList{} = ResultList mempty (FailureInfo (genericLength t) [Expected "notFollowedBy"])
   skipMany p = go
      where go = pure () <|> try p *> go
   unexpected msg = Parser (\t-> ResultList mempty $ FailureInfo (genericLength t) [Expected msg])
   eof = Parser f
      where f rest@((s, _):_)
               | null s = ResultList [ResultsOfLength 0 rest (():|[])] mempty
               | otherwise = ResultList mempty (FailureInfo (genericLength rest) [Expected "end of input"])
            f [] = ResultList [ResultsOfLength 0 [] (():|[])] mempty

instance MonoidNull s => DeterministicParsing (Parser g s) where
   Parser p <<|> Parser q = Parser r where
      r rest = case p rest
               of rl@(ResultList [] _failure) -> rl <> q rest
                  rl -> rl
   takeSome p = (:) <$> p <*> takeMany p
   takeMany (Parser p) = Parser (q 0 id) where
      q !len acc rest = case p rest
                        of ResultList [] _failure -> ResultList [ResultsOfLength len rest (acc [] :| [])] mempty
                           ResultList rl _ -> foldMap continue rl
         where continue (ResultsOfLength len' rest' results) = foldMap (\r-> q (len + len') (acc . (r:)) rest') results
   skipAll (Parser p) = Parser (q 0) where
      q !len rest = case p rest
                    of ResultList [] _failure -> ResultList [ResultsOfLength len rest (():|[])] mempty
                       ResultList rl _failure -> foldMap continue rl
         where continue (ResultsOfLength len' rest' _) = q (len + len') rest'

instance MonoidNull s => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind _ rl@(ResultList [] _) = rl
            rewind t (ResultList rl failure) = ResultList [ResultsOfLength 0 t $ foldr1 (<>) (results <$> rl)] failure
            results (ResultsOfLength _ _ r) = r

instance (Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> ResultList [ResultsOfLength 1 t (first:|[])] mempty
                  _ -> ResultList mempty (FailureInfo (genericLength rest) [Expected "Char.satisfy"])
            p [] = ResultList mempty (FailureInfo 0 [Expected "Char.satisfy"])
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance AmbiguousParsing (Parser g s) where
   ambiguous (Parser p) = Parser q
      where q rest | ResultList rs failure <- p rest = ResultList (groupByLength <$> rs) failure
            groupByLength (ResultsOfLength l rest rs) = ResultsOfLength l rest (Ambiguous rs :| [])

-- | Turns a context-free parser into a backtracking PEG parser that consumes the longest possible prefix of the list
-- of input tails, opposite of 'peg'
longest :: Parser g s a -> Backtrack.Parser g [(s, g (ResultList g s))] a
longest p = Backtrack.Parser q where
   q rest = case applyParser p rest
            of ResultList [] (FailureInfo pos expected) -> Backtrack.NoParse (FailureInfo pos $ map message expected)
               ResultList rs _ -> parsed (last rs)
   parsed (ResultsOfLength l s (r:|_)) = Backtrack.Parsed l r s
   message (Expected msg) = Expected msg
   message (ExpectedInput s) = ExpectedInput [(s, error "longest")]

-- | Turns a backtracking PEG parser of the list of input tails into a context-free parser, opposite of 'longest'
peg :: Backtrack.Parser g [(s, g (ResultList g s))] a -> Parser g s a
peg p = Parser q where
   q rest = case Backtrack.applyParser p rest
            of Backtrack.Parsed l result suffix -> ResultList [ResultsOfLength l suffix (result:|[])] mempty
               Backtrack.NoParse (FailureInfo pos expected) -> ResultList mempty (FailureInfo pos ((fst . head <$>) <$> expected))

-- | Turns a backtracking PEG parser into a context-free parser
terminalPEG :: Monoid s => Backtrack.Parser g s a -> Parser g s a
terminalPEG p = Parser q where
   q [] = case Backtrack.applyParser p mempty
            of Backtrack.Parsed l result _ -> ResultList [ResultsOfLength l [] (result:|[])] mempty
               Backtrack.NoParse failure -> ResultList mempty failure
   q rest@((s, _):_) = case Backtrack.applyParser p s
                       of Backtrack.Parsed l result _ -> 
                             ResultList [ResultsOfLength l (drop l rest) (result:|[])] mempty
                          Backtrack.NoParse failure -> ResultList mempty failure
