{-# LANGUAGE CPP, FlexibleContexts, GeneralizedNewtypeDeriving, InstanceSigs,
             RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Text.Grampa.ContextFree.Memoizing
       {-# DEPRECATED "Use Text.Grampa.ContextFree.SortedMemoizing instead" #-}
       (ResultList(..), Parser(..), BinTree(..),
        reparseTails, longest, peg, terminalPEG)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
#if MIN_VERSION_base(4,13,0)
import Control.Monad (MonadFail(fail))
#endif
import Data.Function (on)
import Data.Foldable (toList)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (maximumBy)
import Data.Monoid (Monoid(mappend, mempty))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid, length, splitPrimePrefix)
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.Ord (Down(Down))
import Data.Semigroup (Semigroup((<>)))
import Data.Semigroup.Cancellative (LeftReductive(isPrefixOf))
import Data.String (fromString)
import Debug.Trace (trace)
import Witherable (Filterable(mapMaybe))

import qualified Text.Parser.Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))

import qualified Rank2

import Text.Grampa.Class (GrammarParsing(..), MultiParsing(..),
                          DeterministicParsing(..), InputParsing(..), InputCharParsing(..),
                          TailsParsing(parseTails), ParseResults, ParseFailure(..), FailureDescription(..), Pos)
import Text.Grampa.Internal (BinTree(..), TraceableParsing(..), expected, erroneous)
import qualified Text.Grampa.PEG.Backtrack.Measured as Backtrack

import Prelude hiding (iterate, length, null, showList, span, takeWhile)

-- | Parser for a context-free grammar with packrat-like sharing of parse results. It does not support left-recursive
-- grammars.
newtype Parser g s r = Parser{applyParser :: [(s, g (ResultList g s))] -> ResultList g s r}

data ResultList g s r = ResultList !(BinTree (ResultInfo g s r)) {-# UNPACK #-} !(ParseFailure Pos s)
data ResultInfo g s r = ResultInfo !Int ![(s, g (ResultList g s))] !r

instance (Show s, Show r) => Show (ResultList g s r) where
   show (ResultList l f) = "ResultList (" ++ shows l (") (" ++ shows f ")")

instance Show s => Show1 (ResultList g s) where
   liftShowsPrec _sp showList _prec (ResultList l f) rest = "ResultList " ++ showList (simplify <$> toList l) (shows f rest)
      where simplify (ResultInfo _ _ r) = r

instance (Show s, Show r) => Show (ResultInfo g s r) where
   show (ResultInfo l _ r) = "(ResultInfo @" ++ show l ++ " " ++ shows r ")"

instance Functor (ResultInfo g s) where
   fmap f (ResultInfo l t r) = ResultInfo l t (f r)

instance Foldable (ResultInfo g s) where
   foldMap f (ResultInfo _ _ r) = f r

instance Traversable (ResultInfo g s) where
   traverse f (ResultInfo l t r) = ResultInfo l t <$> f r

instance Functor (ResultList g s) where
   fmap f (ResultList l failure) = ResultList ((f <$>) <$> l) failure

instance Filterable (ResultList g s) where
   mapMaybe f (ResultList l failure) = ResultList (mapMaybe (traverse f) l) failure

instance Ord s => Semigroup (ResultList g s r) where
   ResultList rl1 f1 <> ResultList rl2 f2 = ResultList (rl1 <> rl2) (f1 <> f2)

instance Ord s => Monoid (ResultList g s r) where
   mempty = ResultList mempty mempty
   mappend = (<>)

instance Functor (Parser g i) where
   fmap f (Parser p) = Parser (fmap f . p)
   {-# INLINABLE fmap #-}

instance Ord s => Applicative (Parser g s) where
   pure a = Parser (\rest-> ResultList (Leaf $ ResultInfo 0 rest a) mempty)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultInfo l rest' f) = continue' l f (q rest')
      continue' l f (ResultList rs failure) = ResultList (adjust l f <$> rs) failure
      adjust l f (ResultInfo l' rest' a) = ResultInfo (l+l') rest' (f a)
   {-# INLINABLE pure #-}
   {-# INLINABLE (<*>) #-}

instance Ord s => Alternative (Parser g s) where
   empty = Parser (\rest-> ResultList mempty $ ParseFailure (Down $ length rest) [] [])
   Parser p <|> Parser q = Parser r where
      r rest = p rest <> q rest
   {-# INLINABLE (<|>) #-}

instance Filterable (Parser g i) where
   mapMaybe f (Parser p) = Parser (mapMaybe f . p)
   {-# INLINABLE mapMaybe #-}

instance Ord s => Monad (Parser g s) where
   return = pure
   Parser p >>= f = Parser q where
      q rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultInfo l rest' a) = continue' l (applyParser (f a) rest')
      continue' l (ResultList rs failure) = ResultList (adjust l <$> rs) failure
      adjust l (ResultInfo l' rest' a) = ResultInfo (l+l') rest' a

#if MIN_VERSION_base(4,13,0)
instance Ord s => MonadFail (Parser g s) where
#endif
   fail msg = Parser p
      where p rest = ResultList mempty (erroneous (Down $ length rest) msg)

instance Ord s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance (Semigroup x, Ord s) => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance (Monoid x, Ord s) => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance (Ord s, LeftReductive s, FactorialMonoid s) => GrammarParsing (Parser g s) where
   type ParserGrammar (Parser g s) = g
   type GrammarFunctor (Parser g s) = ResultList g s
   parsingResult _ = Compose . fromResultList
   nonTerminal f = Parser p where
      p ((_, d) : _) = f d
      p _ = ResultList mempty (expected 0 "NonTerminal at endOfInput")
   {-# INLINE nonTerminal #-}

instance (Ord s, LeftReductive s, FactorialMonoid s) => TailsParsing (Parser g s) where
   parseTails = applyParser

-- | Memoizing parser guarantees O(n²) performance for grammars with unambiguous productions, but provides no left
-- recursion support.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Memoizing.'Parser' g s) -> s -> g ('Compose' ('ParseResults' s) [])
-- @
instance (LeftReductive s, FactorialMonoid s, Ord s) => MultiParsing (Parser g s) where
   type GrammarConstraint (Parser g s) g' = (g ~ g', Rank2.Functor g)
   type ResultFunctor (Parser g s) = Compose (ParseResults s) []
   -- | Returns the list of all possible input prefix parses paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . Compose . fromResultList) (snd $ head $ parseGrammarTails g input)
   -- parseComplete :: (Rank2.Functor g, Eq s, FactorialMonoid s) =>
   --                  g (Parser g s) -> s -> g (Compose (ParseResults s) [])
   parseComplete g input = Rank2.fmap ((snd <$>) . Compose . fromResultList)
                              (snd $ head $ reparseTails close $ parseGrammarTails g input)
      where close = Rank2.fmap (<* eof) g

parseGrammarTails :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> [(s, g (ResultList g s))]
parseGrammarTails g input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d):parsedTail
                  d      = Rank2.fmap (($ parsed) . applyParser) g

reparseTails :: Rank2.Functor g => g (Parser g s) -> [(s, g (ResultList g s))] -> [(s, g (ResultList g s))]
reparseTails _ [] = []
reparseTails final parsed@((s, _):_) = (s, gd):parsed
   where gd = Rank2.fmap (`applyParser` parsed) final

instance (LeftReductive s, FactorialMonoid s, Ord s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   getInput = Parser p
      where p rest@((s, _):_) = ResultList (Leaf $ ResultInfo 0 rest s) mempty
            p [] = ResultList (Leaf $ ResultInfo 0 [] mempty) mempty
   anyToken = Parser p
      where p rest@((s, _):t) = case splitPrimePrefix s
                                of Just (first, _) -> ResultList (Leaf $ ResultInfo 1 t first) mempty
                                   _ -> ResultList mempty (expected (Down $ length rest) "anyToken")
            p [] = ResultList mempty (expected 0 "anyToken")
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case splitPrimePrefix s
               of Just (first, _) | predicate first -> ResultList (Leaf $ ResultInfo 1 t first) mempty
                  _ -> ResultList mempty (expected (Down $ length rest) "satisfy")
            p [] = ResultList mempty (expected 0 "satisfy")
   scan s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = ResultList (Leaf $ ResultInfo l (drop l rest) prefix) mempty
               where (prefix, _, _) = Factorial.spanMaybe' s f i
                     l = Factorial.length prefix
            p _ [] = ResultList (Leaf $ ResultInfo 0 [] mempty) mempty
   take 0 = mempty
   take n = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.take n s, l <- Factorial.length x, l == n =
                    ResultList (Leaf $ ResultInfo l (drop l rest) x) mempty
            p rest = ResultList mempty (expected (Down $ length rest) $ "take " ++ show n)
   takeWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, l <- Factorial.length x =
                    ResultList (Leaf $ ResultInfo l (drop l rest) x) mempty
            p [] = ResultList (Leaf $ ResultInfo 0 [] mempty) mempty
   takeWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, l <- Factorial.length x, l > 0 =
                    ResultList (Leaf $ ResultInfo l (drop l rest) x) mempty
            p rest = ResultList mempty (expected (Down $ length rest) "takeWhile1")
   string s = Parser p where
      p rest@((s', _) : _)
         | s `isPrefixOf` s' = ResultList (Leaf $ ResultInfo l (Factorial.drop l rest) s) mempty
      p rest = ResultList mempty (ParseFailure (Down $ length rest) [LiteralDescription s] [])
      l = Factorial.length s
   notSatisfy predicate = Parser p
      where p rest@((s, _):_)
               | Just (first, _) <- splitPrimePrefix s, 
                 predicate first = ResultList mempty (expected (Down $ length rest) "notSatisfy")
            p rest = ResultList (Leaf $ ResultInfo 0 rest ()) mempty
   {-# INLINABLE string #-}

instance InputParsing (Parser g s)  => TraceableParsing (Parser g s) where
   traceInput description (Parser p) = Parser q
      where q rest@((s, _):_) = case traceWith "Parsing " (p rest)
                                of rl@(ResultList EmptyTree _) -> traceWith "Failed " rl
                                   rl -> traceWith "Parsed " rl
               where traceWith prefix = trace (prefix <> description s)
            q [] = p []

instance (Ord s, Show s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyCharInput predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> ResultList (Leaf $ ResultInfo 1 t $ Factorial.primePrefix s) mempty
                  _ -> ResultList mempty (expected (Down $ length rest) "satisfyCharInput")
            p [] = ResultList mempty (expected 0 "satisfyCharInput")
   scanChars s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = ResultList (Leaf $ ResultInfo l (drop l rest) prefix) mempty
               where (prefix, _, _) = Textual.spanMaybe_' s f i
                     l = Factorial.length prefix
            p _ [] = ResultList (Leaf $ ResultInfo 0 [] mempty) mempty
   takeCharsWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, l <- Factorial.length x =
                    ResultList (Leaf $ ResultInfo l (drop l rest) x) mempty
            p [] = ResultList (Leaf $ ResultInfo 0 [] mempty) mempty
   takeCharsWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, l <- Factorial.length x, l > 0 =
                    ResultList (Leaf $ ResultInfo l (drop l rest) x) mempty
            p rest = ResultList mempty (expected (Down $ length rest) "takeCharsWhile1")
   notSatisfyChar predicate = Parser p
      where p rest@((s, _):_)
               | Just first <- Textual.characterPrefix s, 
                 predicate first = ResultList mempty (expected (Down $ length rest) "notSatisfyChar")
            p rest = ResultList (Leaf $ ResultInfo 0 rest ()) mempty

instance (MonoidNull s, Ord s) => Parsing (Parser g s) where
   try (Parser p) = Parser q
      where q rest = rewindFailure (p rest)
               where rewindFailure (ResultList rl _) = ResultList rl (ParseFailure (Down $ length rest) [] [])
   Parser p <?> msg  = Parser q
      where q rest = replaceFailure (p rest)
               where replaceFailure (ResultList EmptyTree (ParseFailure pos msgs erroneous')) =
                        ResultList EmptyTree (ParseFailure pos
                                                 (if pos == Down (length rest) then [StaticDescription msg]
                                                  else msgs)
                                                 erroneous')
                     replaceFailure rl = rl
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList EmptyTree _) = ResultList (Leaf $ ResultInfo 0 t ()) mempty
            rewind t ResultList{} = ResultList mempty (expected (Down $ length t) "notFollowedBy")
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = Parser (\t-> ResultList mempty $ expected (Down $ length t) msg)
   eof = Parser f
      where f rest@((s, _):_)
               | null s = ResultList (Leaf $ ResultInfo 0 rest ()) mempty
               | otherwise = ResultList mempty (expected (Down $ length rest) "endOfInput")
            f [] = ResultList (Leaf $ ResultInfo 0 [] ()) mempty

instance (MonoidNull s, Ord s) => DeterministicParsing (Parser g s) where
   Parser p <<|> Parser q = Parser r where
      r rest = case p rest
               of rl@(ResultList EmptyTree _failure) -> rl <> q rest
                  rl -> rl
   takeSome p = (:) <$> p <*> takeMany p
   takeMany (Parser p) = Parser (q 0 id) where
      q len acc rest = case p rest
                       of ResultList EmptyTree _failure -> ResultList (Leaf $ ResultInfo len rest (acc [])) mempty
                          ResultList rl _ -> foldMap continue rl
         where continue (ResultInfo len' rest' result) = q (len + len') (acc . (result:)) rest'
   skipAll (Parser p) = Parser (q 0) where
      q len rest = case p rest
                   of ResultList EmptyTree _failure -> ResultList (Leaf $ ResultInfo len rest ()) mempty
                      ResultList rl _failure -> foldMap continue rl
         where continue (ResultInfo len' rest' _) = q (len + len') rest'

instance (MonoidNull s, Ord s) => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList rl failure) = ResultList (rewindInput t <$> rl) failure
            rewindInput t (ResultInfo _ _ r) = ResultInfo 0 t r

instance (Ord s, Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> ResultList (Leaf $ ResultInfo 1 t first) mempty
                  _ -> ResultList mempty (expected (Down $ length rest) "Char.satisfy")
            p [] = ResultList mempty (expected 0 "Char.satisfy")
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

fromResultList :: FactorialMonoid s => ResultList g s r -> ParseResults s [(s, r)]
fromResultList (ResultList EmptyTree (ParseFailure pos positive negative)) =
   Left (ParseFailure (pos - 1) positive negative)
fromResultList (ResultList rl _failure) = Right (f <$> toList rl)
   where f (ResultInfo _ ((s, _):_) r) = (s, r)
         f (ResultInfo _ [] r) = (mempty, r)

-- | Turns a context-free parser into a backtracking PEG parser that consumes the longest possible prefix of the list
-- of input tails, opposite of 'peg'
longest :: Parser g s a -> Backtrack.Parser g [(s, g (ResultList g s))] a
longest p = Backtrack.Parser q where
   q rest = case applyParser p rest
            of ResultList EmptyTree (ParseFailure pos positive negative)
                  -> Backtrack.NoParse (ParseFailure pos (map message positive) (map message negative))
               ResultList rs _ -> parsed (maximumBy (compare `on` resultLength) rs)
   resultLength (ResultInfo l _ _) = l
   parsed (ResultInfo l s r) = Backtrack.Parsed l r s
   message (StaticDescription msg) = StaticDescription msg
   message (LiteralDescription s) = LiteralDescription [(s, error "longest")]

-- | Turns a backtracking PEG parser of the list of input tails into a context-free parser, opposite of 'longest'
peg :: Ord s => Backtrack.Parser g [(s, g (ResultList g s))] a -> Parser g s a
peg p = Parser q where
   q rest = case Backtrack.applyParser p rest
            of Backtrack.Parsed l result suffix -> ResultList (Leaf $ ResultInfo l suffix result) mempty
               Backtrack.NoParse (ParseFailure pos positive negative)
                  -> ResultList mempty (ParseFailure pos (original <$> positive) (original <$> negative))
      where original = (fst . head <$>)

-- | Turns a backtracking PEG parser into a context-free parser
terminalPEG :: (Monoid s, Ord s) => Backtrack.Parser g s a -> Parser g s a
terminalPEG p = Parser q where
   q [] = case Backtrack.applyParser p mempty
            of Backtrack.Parsed l result _ -> ResultList (Leaf $ ResultInfo l [] result) mempty
               Backtrack.NoParse failure -> ResultList mempty failure
   q rest@((s, _):_) = case Backtrack.applyParser p s
                       of Backtrack.Parsed l result _ -> ResultList (Leaf $ ResultInfo l (drop l rest) result) mempty
                          Backtrack.NoParse failure -> ResultList mempty failure
