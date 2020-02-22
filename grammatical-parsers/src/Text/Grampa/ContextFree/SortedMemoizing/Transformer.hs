{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, InstanceSigs,
             RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Text.Grampa.ContextFree.SortedMemoizing.Transformer
       (FailureInfo(..), ResultList(..), ParserT(..), (<<|>),
        reparseTails, longest, peg, terminalPEG)
where

import Control.Applicative
import Control.Monad (MonadPlus(..), void)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import Data.List (genericLength, nub)
import Data.List.NonEmpty (NonEmpty((:|)), groupBy, fromList, toList)
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid, splitPrimePrefix)
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.Semigroup.Cancellative (LeftReductive(isPrefixOf))
import Data.String (fromString)

import qualified Text.Parser.Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))

import qualified Rank2

import Text.Grampa.Class (GrammarParsing(..), InputParsing(..), InputCharParsing(..), MultiParsing(..),
                          AmbiguousParsing(..), Ambiguous(Ambiguous), ParseResults, ParseFailure(..), Expected(..))
import Text.Grampa.Internal (FailureInfo(..))
import qualified Text.Grampa.PEG.Backtrack.Measured as Backtrack

import Prelude hiding (iterate, length, null, showList, span, takeWhile)

-- | Parser for a context-free grammar with packrat-like sharing of parse results. It does not support left-recursive
-- grammars.
newtype ParserT m g s r = Parser{applyParser :: [(s, g (ResultList m g s))] -> ResultList m g s r}

data ResultsOfLength m g s r = ResultsOfLength !Int ![(s, g (ResultList m g s))] !(NonEmpty (m r))

data ResultList m g s r = ResultList ![ResultsOfLength m g s r] !(FailureInfo s)

instance Functor m => Functor (ParserT m g s) where
   fmap f (Parser p) = Parser (fmap f . p)
   {-# INLINE fmap #-}

instance Applicative m => Applicative (ParserT m g s) where
   pure a = Parser (\rest-> ResultList [ResultsOfLength 0 rest (pure a:|[])] mempty)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultsOfLength l rest' fs) = foldMap (continue' l $ q rest') fs
      continue' l (ResultList rs failure) f = ResultList (adjust l f <$> rs) failure
      adjust l f (ResultsOfLength l' rest' as) = ResultsOfLength (l+l') rest' ((f <*>) <$> as)
   {-# INLINABLE pure #-}
   {-# INLINABLE (<*>) #-}

instance Applicative m => Alternative (ParserT m g s) where
   empty = Parser (\rest-> ResultList mempty $ FailureInfo (genericLength rest) [])
   Parser p <|> Parser q = Parser r where
      r rest = p rest <> q rest
   {-# INLINE (<|>) #-}
   {-# INLINABLE empty #-}

infixl 3 <<|>
(<<|>) :: ParserT m g s a -> ParserT m g s a -> ParserT m g s a
Parser p <<|> Parser q = Parser r where
   r rest = case p rest
            of rl@(ResultList [] _failure) -> rl <> q rest
               rl -> rl

instance Monad m => Monad (ParserT m g s) where
   return = pure
   (>>) = (*>)
   Parser p >>= f = Parser q where
      q rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultsOfLength l rest' rs) = foldMap (continue' l . flip applyParser rest' . (>>= f) . lift) rs
      continue' l (ResultList rs failure) = ResultList (adjust l <$> rs) failure
      adjust l (ResultsOfLength l' rest' rs) = ResultsOfLength (l+l') rest' rs

instance Monad m => MonadPlus (ParserT m g s) where
   mzero = empty
   mplus = (<|>)

lift :: m a -> ParserT m g s a
lift m = Parser (\rest-> ResultList [ResultsOfLength 0 rest (m:|[])] mempty)

instance (Applicative m, Semigroup x) => Semigroup (ParserT m g s x) where
   (<>) = liftA2 (<>)

instance (Applicative m, Monoid x) => Monoid (ParserT m g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance (Applicative m, LeftReductive s, FactorialMonoid s, Rank2.Functor g) => GrammarParsing (ParserT m g s) where
   type ParserGrammar (ParserT m g s) = g
   type GrammarFunctor (ParserT m g s) = ResultList m g s
   nonTerminal :: (ParserInput (ParserT m g s) ~ s) => (g (ResultList m g s) -> ResultList m g s a) -> ParserT m g s a
   nonTerminal f = Parser p where
      p ((_, d) : _) = f d
      p _ = ResultList mempty (FailureInfo 0 [Expected "NonTerminal at endOfInput"])
   {-# INLINE nonTerminal #-}

-- | Memoizing parser guarantees O(n²) performance for grammars with unambiguous productions, but provides no left
-- recursion support.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Memoizing.'Parser' g s) -> s -> g ('Compose' ('ParseResults' s) [])
-- @
instance (Applicative m, LeftReductive s, FactorialMonoid s) => MultiParsing (ParserT m g s) where
   type GrammarConstraint (ParserT m g s) g' = (g ~ g', Rank2.Functor g)
   type ResultFunctor (ParserT m g s) = Compose (Compose (ParseResults s) []) m
   -- | Returns the list of all possible input prefix parses paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . Compose . Compose . fmap (fmap sequenceA) . fromResultList input)
                                    (snd $ head $ parseTails g input)
   parseComplete :: (ParserInput (ParserT m g s) ~ s, Rank2.Functor g, Eq s, FactorialMonoid s) =>
                    g (ParserT m g s) -> s -> g (Compose (Compose (ParseResults s) []) m)
   parseComplete g input = Rank2.fmap (Compose . fmap snd . Compose . fromResultList input)
                              (snd $ head $ reparseTails close $ parseTails g input)
      where close = Rank2.fmap (<* eof) g

parseTails :: (Rank2.Functor g, FactorialMonoid s) => g (ParserT m g s) -> s -> [(s, g (ResultList m g s))]
parseTails g input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d):parsedTail
                  d      = Rank2.fmap (($ parsed) . applyParser) g

reparseTails :: Rank2.Functor g => g (ParserT m g s) -> [(s, g (ResultList m g s))] -> [(s, g (ResultList m g s))]
reparseTails _ [] = []
reparseTails final parsed@((s, _):_) = (s, gd):parsed
   where gd = Rank2.fmap (`applyParser` parsed) final

instance (Applicative m, LeftReductive s, FactorialMonoid s) => InputParsing (ParserT m g s) where
   type ParserInput (ParserT m g s) = s
   endOfInput = eof
   getInput = Parser p
      where p rest@((s, _):_) = ResultList [ResultsOfLength 0 rest (pure s:|[])] mempty
            p [] = ResultList [ResultsOfLength 0 [] (pure mempty:|[])] mempty
   anyToken = Parser p
      where p rest@((s, _):t) = case splitPrimePrefix s
                                of Just (first, _) -> ResultList [ResultsOfLength 1 t (pure first:|[])] mempty
                                   _ -> ResultList mempty (FailureInfo (genericLength rest) [Expected "anyToken"])
            p [] = ResultList mempty (FailureInfo 0 [Expected "anyToken"])
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case splitPrimePrefix s
               of Just (first, _) | predicate first -> ResultList [ResultsOfLength 1 t (pure first:|[])] mempty
                  _ -> ResultList mempty (FailureInfo (genericLength rest) [Expected "satisfy"])
            p [] = ResultList mempty (FailureInfo 0 [Expected "satisfy"])
   scan s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = ResultList [ResultsOfLength l (drop l rest) (pure prefix:|[])] mempty
               where (prefix, _, _) = Factorial.spanMaybe' s f i
                     l = Factorial.length prefix
            p _ [] = ResultList [ResultsOfLength 0 [] (pure mempty:|[])] mempty
   takeWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, l <- Factorial.length x =
                    ResultList [ResultsOfLength l (drop l rest) (pure x:|[])] mempty
            p [] = ResultList [ResultsOfLength 0 [] (pure mempty:|[])] mempty
   takeWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, l <- Factorial.length x, l > 0 =
                    ResultList [ResultsOfLength l (drop l rest) (pure x:|[])] mempty
            p rest = ResultList mempty (FailureInfo (genericLength rest) [Expected "takeWhile1"])
   string s = Parser p where
      p rest@((s', _) : _)
         | s `isPrefixOf` s' = ResultList [ResultsOfLength l (Factorial.drop l rest) (pure s:|[])] mempty
      p rest = ResultList mempty (FailureInfo (genericLength rest) [ExpectedInput s])
      l = Factorial.length s
   notSatisfy predicate = Parser p
      where p rest@((s, _):_)
               | Just (first, _) <- splitPrimePrefix s, 
                 predicate first = ResultList mempty (FailureInfo (genericLength rest) [Expected "notSatisfy"])
            p rest = ResultList [ResultsOfLength 0 rest (pure ():|[])] mempty
   {-# INLINABLE string #-}

instance (Applicative m, Show s, TextualMonoid s) => InputCharParsing (ParserT m g s) where
   satisfyCharInput predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first
                     | predicate first -> ResultList [ResultsOfLength 1 t (pure (Factorial.primePrefix s):|[])] mempty
                  _ -> ResultList mempty (FailureInfo (genericLength rest) [Expected "satisfyCharInput"])
            p [] = ResultList mempty (FailureInfo 0 [Expected "satisfyCharInput"])
   scanChars s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = ResultList [ResultsOfLength l (drop l rest) (pure prefix:|[])] mempty
               where (prefix, _, _) = Textual.spanMaybe_' s f i
                     l = Factorial.length prefix
            p _ [] = ResultList [ResultsOfLength 0 [] (pure mempty:|[])] mempty
   takeCharsWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, l <- Factorial.length x =
                    ResultList [ResultsOfLength l (drop l rest) (pure x:|[])] mempty
            p [] = ResultList [ResultsOfLength 0 [] (pure mempty:|[])] mempty
   takeCharsWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, l <- Factorial.length x, l > 0 =
                    ResultList [ResultsOfLength l (drop l rest) (pure x:|[])] mempty
            p rest = ResultList mempty (FailureInfo (genericLength rest) [Expected "takeCharsWhile1"])
   notSatisfyChar predicate = Parser p
      where p rest@((s, _):_)
               | Just first <- Textual.characterPrefix s, 
                 predicate first = ResultList mempty (FailureInfo (genericLength rest) [Expected "notSatisfyChar"])
            p rest = ResultList [ResultsOfLength 0 rest (pure ():|[])] mempty

instance (Applicative m, MonoidNull s) => Parsing (ParserT m g s) where
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
      where rewind t (ResultList [] _) = ResultList [ResultsOfLength 0 t (pure ():|[])] mempty
            rewind t ResultList{} = ResultList mempty (FailureInfo (genericLength t) [Expected "notFollowedBy"])
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = Parser (\t-> ResultList mempty $ FailureInfo (genericLength t) [Expected msg])
   eof = Parser f
      where f rest@((s, _):_)
               | null s = ResultList [ResultsOfLength 0 rest (pure ():|[])] mempty
               | otherwise = ResultList mempty (FailureInfo (genericLength rest) [Expected "end of input"])
            f [] = ResultList [ResultsOfLength 0 [] (pure ():|[])] mempty

instance (Applicative m, MonoidNull s) => LookAheadParsing (ParserT m g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind _ rl@(ResultList [] _) = rl
            rewind t (ResultList rl failure) = ResultList [ResultsOfLength 0 t $ foldr1 (<>) (results <$> rl)] failure
            results (ResultsOfLength _ _ r) = r

instance (Applicative m, Show s, TextualMonoid s) => CharParsing (ParserT m g s) where
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> ResultList [ResultsOfLength 1 t (pure first:|[])] mempty
                  _ -> ResultList mempty (FailureInfo (genericLength rest) [Expected "Char.satisfy"])
            p [] = ResultList mempty (FailureInfo 0 [Expected "Char.satisfy"])
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Applicative m, Eq (m ())) => AmbiguousParsing (ParserT m g s) where
   ambiguous (Parser p) = Parser q
      where q rest | ResultList rs failure <- p rest = ResultList (groupByLength <$> rs) failure
            groupByLength :: ResultsOfLength m g s r -> ResultsOfLength m g s (Ambiguous r)
            groupByLength (ResultsOfLength l rest rs) =
               ResultsOfLength l rest ((Ambiguous <$>) <$> fromList (sequenceA <$> groupBy ((==) `on` void) rs))

-- | Turns a context-free parser into a backtracking PEG parser that consumes the longest possible prefix of the list
-- of input tails, opposite of 'peg'
longest :: ParserT Identity g s a -> Backtrack.Parser g [(s, g (ResultList Identity g s))] a
longest p = Backtrack.Parser q where
   q rest = case applyParser p rest
            of ResultList [] (FailureInfo pos expected) -> Backtrack.NoParse (FailureInfo pos $ map message expected)
               ResultList rs _ -> parsed (last rs)
   parsed (ResultsOfLength l s (Identity r:|_)) = Backtrack.Parsed l r s
   message (Expected msg) = Expected msg
   message (ExpectedInput s) = ExpectedInput [(s, error "longest")]

-- | Turns a backtracking PEG parser of the list of input tails into a context-free parser, opposite of 'longest'
peg :: Applicative m => Backtrack.Parser g [(s, g (ResultList m g s))] a -> ParserT m g s a
peg p = Parser q where
   q rest = case Backtrack.applyParser p rest
            of Backtrack.Parsed l result suffix -> ResultList [ResultsOfLength l suffix (pure result:|[])] mempty
               Backtrack.NoParse (FailureInfo pos expected) -> ResultList mempty (FailureInfo pos ((fst . head <$>) <$> expected))

-- | Turns a backtracking PEG parser into a context-free parser
terminalPEG :: (Applicative m, Monoid s) => Backtrack.Parser g s a -> ParserT m g s a
terminalPEG p = Parser q where
   q [] = case Backtrack.applyParser p mempty
            of Backtrack.Parsed l result _ -> ResultList [ResultsOfLength l [] (pure result:|[])] mempty
               Backtrack.NoParse failure -> ResultList mempty failure
   q rest@((s, _):_) = case Backtrack.applyParser p s
                       of Backtrack.Parsed l result _ -> 
                             ResultList [ResultsOfLength l (drop l rest) (pure result:|[])] mempty
                          Backtrack.NoParse failure -> ResultList mempty failure

fromResultList :: (Functor m, Eq s, FactorialMonoid s) => s -> ResultList m g s r -> ParseResults s [(s, m r)]
fromResultList s (ResultList [] (FailureInfo pos msgs)) =
   Left (ParseFailure (Factorial.length s - pos + 1) (nub msgs))
fromResultList _ (ResultList rl _failure) = Right (foldMap f rl)
   where f (ResultsOfLength _ ((s, _):_) r) = (,) s <$> toList r
         f (ResultsOfLength _ [] r) = (,) mempty <$> toList r
{-# INLINABLE fromResultList #-}

instance Functor m => Functor (ResultsOfLength m g s) where
   fmap f (ResultsOfLength l t r) = ResultsOfLength l t ((f <$>) <$> r)
   {-# INLINE fmap #-}

instance Functor m => Functor (ResultList m g s) where
   fmap f (ResultList l failure) = ResultList ((f <$>) <$> l) failure
   {-# INLINE fmap #-}

instance Semigroup (ResultList m g s r) where
   ResultList rl1 f1 <> ResultList rl2 f2 = ResultList (join rl1 rl2) (f1 <> f2)
      where join [] rl = rl
            join rl [] = rl
            join rl1'@(rol1@(ResultsOfLength l1 s1 r1) : rest1) rl2'@(rol2@(ResultsOfLength l2 _ r2) : rest2)
               | l1 < l2 = rol1 : join rest1 rl2'
               | l1 > l2 = rol2 : join rl1' rest2
               | otherwise = ResultsOfLength l1 s1 (r1 <> r2) : join rest1 rest2

instance Monoid (ResultList m g s r) where
   mempty = ResultList mempty mempty
   mappend = (<>)
