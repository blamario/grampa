{-# LANGUAGE BangPatterns, CPP, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, InstanceSigs,
             RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
-- | A context-free memoizing parser that handles all alternatives in parallel
-- and carries a monadic computation with each parsing result.
module Text.Grampa.ContextFree.SortedMemoizing.Transformer (ResultListT(..), ParserT(..), (<<|>),
                                                            tbind, lift, tmap, longest, peg, terminalPEG)
where

import Control.Applicative
import Control.Monad (MonadPlus(..), join, void)
#if MIN_VERSION_base(4,13,0)
import Control.Monad (MonadFail(fail))
#endif
import qualified Control.Monad.Trans.Class as Trans (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT)
import Data.Either (partitionEithers)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty((:|)), groupBy, nonEmpty, fromList, toList)
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid, splitPrimePrefix)
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.Ord (Down(Down))
import Data.Semigroup (Semigroup((<>)))
import Data.Semigroup.Cancellative (LeftReductive(isPrefixOf))
import Data.String (fromString)
import Witherable (Filterable(mapMaybe))
import Debug.Trace (trace)

import qualified Text.Parser.Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))

import qualified Rank2

import Text.Grampa.Class (GrammarParsing(..), InputParsing(..), InputCharParsing(..), MultiParsing(..),
                          ConsumedInputParsing(..), CommittedParsing(..), DeterministicParsing(..),
                          AmbiguousParsing(..), Ambiguous(Ambiguous),
                          TailsParsing(..), ParseResults, ParseFailure(..), FailureDescription(..), Pos)
import Text.Grampa.Internal (expected, FallibleResults(..), AmbiguousAlternative(..), TraceableParsing(..))
import qualified Text.Grampa.PEG.Backtrack.Measured as Backtrack

import Prelude hiding (iterate, null, showList, span, takeWhile)

-- | Parser for a context-free grammar with packrat-like sharing that carries a monadic computation as part of the
-- parse result.
newtype ParserT m g s r = Parser{applyParser :: [(s, g (ResultListT m g s))] -> ResultListT m g s r}

newtype ResultsOfLengthT m g s r = ResultsOfLengthT{getResultsOfLength :: ResultsOfLength m g s (m r)}
data ResultsOfLength m g s a = ROL !Int ![(s, g (ResultListT m g s))] !(NonEmpty a)
data ResultListT m g s r = ResultList{resultSuccesses :: ![ResultsOfLengthT m g s r],
                                      resultFailures  :: !(ParseFailure Pos s)}

singleResult :: (Applicative m, Ord s) => Int -> [(s, g (ResultListT m g s))] -> r -> ResultListT m g s r
singleResult len rest a = ResultList [ResultsOfLengthT $ ROL len rest (pure a:|[])] mempty

instance Functor m => Functor (ParserT m g s) where
   fmap f (Parser p) = Parser (fmap f . p)
   {-# INLINE fmap #-}

instance (Applicative m, Ord s) => Applicative (ParserT m g s) where
   pure a = Parser (\rest-> singleResult 0 rest a)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultsOfLengthT (ROL l rest' fs)) = foldMap (continue' l $ q rest') fs
      continue' l (ResultList rs failure) f = ResultList (adjust l f <$> rs) failure
      adjust l f (ResultsOfLengthT (ROL l' rest' as)) = ResultsOfLengthT (ROL (l+l') rest' ((f <*>) <$> as))
   {-# INLINABLE pure #-}
   {-# INLINABLE (<*>) #-}

instance (Applicative m, Ord s) => Alternative (ParserT m g s) where
   empty = Parser (\rest-> ResultList mempty $ ParseFailure (Down $ length rest) [] [])
   Parser p <|> Parser q = Parser r where
      r rest = p rest <> q rest
   {-# INLINE (<|>) #-}
   {-# INLINABLE empty #-}

instance (Applicative m, Traversable m) => Filterable (ParserT m g s) where
  mapMaybe f (Parser p) = Parser (mapMaybe f . p)

-- | The 'StateT' instance dangerously assumes that the filtered parser is stateless.
instance {-# overlaps #-} (Monad m, Traversable m, Monoid state) => Filterable (ParserT (StateT state m) g s) where
  mapMaybe f (Parser p) = Parser (mapMaybe f . p)

instance (Monad m, Traversable m, Ord s) => Monad (ParserT m g s) where
   return = pure
   (>>) = (*>)
   Parser p >>= f = Parser q where
      q rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultsOfLengthT (ROL l rest' rs)) = foldMap (continue' l . flip applyParser rest' . rejoin . fmap f) rs
      continue' l (ResultList rs failure) = ResultList (adjust l <$> rs) failure
      adjust l (ResultsOfLengthT (ROL l' rest' rs)) = ResultsOfLengthT (ROL (l+l') rest' rs)
      rejoin :: forall a. m (ParserT m g s a) -> ParserT m g s a
      rejoinResults :: forall a. m (ResultListT m g s a) -> ResultListT m g s a
      rejoinResultsOfLengthT :: forall a. m (ResultsOfLengthT m g s a) -> ResultsOfLengthT m g s a
      rejoin m = Parser (\rest-> rejoinResults $ flip applyParser rest <$> m)
      rejoinResults m = ResultList (fmap rejoinResultsOfLengthT $ sequence $ resultSuccesses <$> m) (foldMap resultFailures m)
      rejoinResultsOfLengthT m = ResultsOfLengthT (join <$> traverse getResultsOfLength m)

#if MIN_VERSION_base(4,13,0)
instance (Monad m, Traversable m, Ord s) => MonadFail (ParserT m g s) where
#endif
   fail msg = Parser p
      where p rest = ResultList mempty (ParseFailure (Down $ length rest) [] [StaticDescription msg])

instance (Foldable m, Monad m, Traversable m, Ord s) => MonadPlus (ParserT m g s) where
   mzero = empty
   mplus = (<|>)

-- | Lift a parse-free computation into the parser.
lift :: Ord s => m a -> ParserT m g s a
lift m = Parser (\rest-> ResultList [ResultsOfLengthT $ ROL 0 rest (m:|[])] mempty)

-- | Transform the computation carried by the parser using the monadic bind ('>>=').
tbind :: Monad m => ParserT m g s a -> (a -> m b) -> ParserT m g s b
tbind (Parser p) f = Parser (bindResultList f . p)

-- | Transform the computation carried by the parser.
tmap :: (m a -> m b) -> ParserT m g s a -> ParserT m g s b
tmap f (Parser p) = Parser (mapResultList f . p)

bindResultList :: Monad m => (a -> m b) -> ResultListT m g s a -> ResultListT m g s b
bindResultList f (ResultList successes failures) = ResultList (bindResults f <$> successes) failures

mapResultList :: (m a -> m b) -> ResultListT m g s a -> ResultListT m g s b
mapResultList f (ResultList successes failures) = ResultList (mapResults f <$> successes) failures

bindResults :: Monad m => (a -> m b) -> ResultsOfLengthT m g s a -> ResultsOfLengthT m g s b
bindResults f (ResultsOfLengthT (ROL len rest as)) = ResultsOfLengthT (ROL len rest ((>>= f) <$> as))

mapResults :: (m a -> m b) -> ResultsOfLengthT m g s a -> ResultsOfLengthT m g s b
mapResults f (ResultsOfLengthT rol) = ResultsOfLengthT (f <$> rol)

instance (Applicative m, Semigroup x, Ord s) => Semigroup (ParserT m g s x) where
   (<>) = liftA2 (<>)

instance (Applicative m, Monoid x, Ord s) => Monoid (ParserT m g s x) where
   mempty = pure mempty
   mappend = (<>)

-- | Memoizing parser that carries an applicative computation. Can be wrapped with
-- 'Text.Grampa.ContextFree.LeftRecursive.Fixed' to provide left recursion support.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Memoizing.'Parser' g s) -> s -> g ('Compose' ('ParseResults' s) [])
-- @
instance (Applicative m, LeftReductive s, FactorialMonoid s, Ord s) => MultiParsing (ParserT m g s) where
   type GrammarConstraint (ParserT m g s) g' = (g ~ g', Rank2.Functor g)
   type ResultFunctor (ParserT m g s) = Compose (Compose (ParseResults s) []) m
   -- | Returns the list of all possible input prefix parses paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . Compose . Compose . fmap (fmap sequenceA) . fromResultList)
                                    (snd $ head $ parseGrammarTails g input)
   -- parseComplete :: (ParserInput (ParserT m g s) ~ s, Rank2.Functor g, Eq s, FactorialMonoid s) =>
   --                  g (ParserT m g s) -> s -> g (Compose (Compose (ParseResults s) []) m)
   parseComplete g input = Rank2.fmap (Compose . fmap snd . Compose . fromResultList)
                              (snd $ head $ parseAllTails close $ parseGrammarTails g input)
      where close = Rank2.fmap (<* eof) g

-- | Memoizing parser that carries an applicative computation. Can be wrapped with
-- 'Text.Grampa.ContextFree.LeftRecursive.Fixed' to provide left recursion support.
instance (Applicative m, Ord s, LeftReductive s, FactorialMonoid s) => GrammarParsing (ParserT m g s) where
   type ParserGrammar (ParserT m g s) = g
   type GrammarFunctor (ParserT m g s) = ResultListT m g s
   parsingResult _ = Compose . Compose . fmap (fmap sequenceA) . fromResultList
   nonTerminal :: (ParserInput (ParserT m g s) ~ s) => (g (ResultListT m g s) -> ResultListT m g s a) -> ParserT m g s a
   nonTerminal f = Parser p where
      p input@((_, d) : _) = ResultList rs' failure
         where ResultList rs failure = f d
               rs' = sync <$> rs
               -- in left-recursive grammars the stored input remainder may be wrong, so revert to the complete input
               sync (ResultsOfLengthT (ROL 0 _remainder r)) = ResultsOfLengthT (ROL 0 input r)
               sync rols = rols
      p _ = ResultList mempty (expected 0 "NonTerminal at endOfInput")
   {-# INLINE nonTerminal #-}

instance (Applicative m, Ord s, LeftReductive s, FactorialMonoid s, Rank2.Functor g) =>
         TailsParsing (ParserT m g s) where
   parseTails = applyParser

parseGrammarTails :: (Rank2.Functor g, FactorialMonoid s) => g (ParserT m g s) -> s -> [(s, g (ResultListT m g s))]
parseGrammarTails g input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d):parsedTail
                  d      = Rank2.fmap (($ parsed) . applyParser) g

instance (Applicative m, LeftReductive s, FactorialMonoid s, Ord s) => InputParsing (ParserT m g s) where
   type ParserInput (ParserT m g s) = s
   getInput = Parser p
      where p rest@((s, _):_) = singleResult 0 rest s
            p [] = singleResult 0 [] mempty
   anyToken = Parser p
      where p rest@((s, _):t) = case splitPrimePrefix s
                                of Just (first, _) -> singleResult 1 t first
                                   _ -> ResultList mempty (expected (Down $ length rest) "anyToken")
            p [] = ResultList mempty (expected 0 "anyToken")
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case splitPrimePrefix s
               of Just (first, _) | predicate first -> singleResult 1 t first
                  _ -> ResultList mempty (expected (Down $ length rest) "satisfy")
            p [] = ResultList mempty (expected 0 "satisfy")
   scan s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = singleResult l (drop l rest) prefix
               where (prefix, _, _) = Factorial.spanMaybe' s f i
                     l = Factorial.length prefix
            p _ [] = singleResult 0 [] mempty
   takeWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, l <- Factorial.length x =
                    singleResult l (drop l rest) x
            p [] = singleResult 0 [] mempty
   take 0 = mempty
   take n = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.take n s, l <- Factorial.length x, l == n =
                    singleResult l (drop l rest) x
            p rest = ResultList mempty (expected (Down $ length rest) $ "take " ++ show n)
   takeWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, l <- Factorial.length x, l > 0 =
                    singleResult l (drop l rest) x
            p rest = ResultList mempty (expected (Down $ length rest) "takeWhile1")
   string s = Parser p where
      p rest@((s', _) : _)
         | s `isPrefixOf` s' = singleResult l (drop l rest) s
      p rest = ResultList mempty (ParseFailure (Down $ length rest) [LiteralDescription s] [])
      l = Factorial.length s
   notSatisfy predicate = Parser p
      where p rest@((s, _):_)
               | Just (first, _) <- splitPrimePrefix s, 
                 predicate first = ResultList mempty (expected (Down $ length rest) "notSatisfy")
            p rest = singleResult 0 rest ()
   {-# INLINABLE string #-}

instance InputParsing (ParserT m g s) => TraceableParsing (ParserT m g s) where
   traceInput description (Parser p) = Parser q
      where q rest = case traceWith "Parsing " (p rest)
                     of rl@(ResultList [] _) -> traceWith "Failed " rl
                        rl -> traceWith "Parsed " rl
               where traceWith prefix = trace (prefix <> case rest of ((s, _):_) -> description s; [] -> "EOF")

instance (Applicative m, Ord s, Show s, TextualMonoid s) => InputCharParsing (ParserT m g s) where
   satisfyCharInput predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first
                     | predicate first -> singleResult 1 t (Factorial.primePrefix s)
                  _ -> ResultList mempty (expected (Down $ length rest) "satisfyCharInput")
            p [] = ResultList mempty (expected 0 "satisfyCharInput")
   scanChars s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = singleResult l (drop l rest) prefix
               where (prefix, _, _) = Textual.spanMaybe_' s f i
                     l = Factorial.length prefix
            p _ [] = singleResult 0 [] mempty
   takeCharsWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, l <- Factorial.length x =
                    singleResult l (drop l rest) x
            p [] = singleResult 0 [] mempty
   takeCharsWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, l <- Factorial.length x, l > 0 =
                    singleResult l (drop l rest) x
            p rest = ResultList mempty (expected (Down $ length rest) "takeCharsWhile1")
   notSatisfyChar predicate = Parser p
      where p rest@((s, _):_)
               | Just first <- Textual.characterPrefix s, 
                 predicate first = ResultList mempty (expected (Down $ length rest) "notSatisfyChar")
            p rest = singleResult 0 rest ()

instance (Applicative m, LeftReductive s, FactorialMonoid s, Ord s) => ConsumedInputParsing (ParserT m g s) where
   match (Parser p) = Parser q
      where q [] = addConsumed mempty (p [])
            q rest@((s, _) : _) = addConsumed s (p rest)
            addConsumed input (ResultList rl failure) = ResultList (add1 <$> rl) failure
               where add1 (ResultsOfLengthT (ROL l t rs)) =
                        ResultsOfLengthT (ROL l t $ ((,) (Factorial.take l input) <$>) <$> rs)

instance (Applicative m, MonoidNull s, Ord s) => Parsing (ParserT m g s) where
   try (Parser p) = Parser q
      where q rest = rewindFailure (p rest)
               where rewindFailure (ResultList rl _) = ResultList rl (ParseFailure (Down $ length rest) [] [])
   Parser p <?> msg  = Parser q
      where q rest = replaceFailure (p rest)
               where replaceFailure (ResultList [] (ParseFailure pos msgs erroneous)) =
                        ResultList [] (ParseFailure pos (if pos == Down (length rest) then [StaticDescription msg]
                                                         else msgs) erroneous)
                     replaceFailure rl = rl
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList [] _) = singleResult 0 t ()
            rewind t ResultList{} = ResultList mempty (expected (Down $ length t) "notFollowedBy")
   skipMany p = go
      where go = pure () <|> try p *> go
   unexpected msg = Parser (\t-> ResultList mempty $ expected (Down $ length t) msg)
   eof = Parser f
      where f rest@((s, _):_)
               | null s = singleResult 0 rest ()
               | otherwise = ResultList mempty (expected (Down $ length rest) "end of input")
            f [] = singleResult 0 [] ()

instance (Applicative m, MonoidNull s, Ord s) => DeterministicParsing (ParserT m g s) where
   Parser p <<|> Parser q = Parser r where
      r rest = case p rest
               of rl@(ResultList [] _failure) -> rl <> q rest
                  rl -> rl
   takeSome p = (:) <$> p <*> takeMany p
   takeMany (Parser p) = Parser (q 0 (pure id)) where
      q !len acc rest = case p rest
                        of ResultList [] _failure
                              -> ResultList [ResultsOfLengthT $ ROL len rest (fmap ($ []) acc :| [])] mempty
                           ResultList rl _ -> foldMap continue rl
         where continue (ResultsOfLengthT (ROL len' rest' results)) =
                  foldMap (\r-> q (len + len') (liftA2 (.) acc ((:) <$> r)) rest') results
   skipAll (Parser p) = Parser (q 0 (pure ())) where
      q !len effects rest = case p rest
                       of ResultList [] _failure -> ResultList [ResultsOfLengthT $ ROL len rest (effects:|[])] mempty
                          ResultList rl _failure -> foldMap continue rl
         where continue (ResultsOfLengthT (ROL len' rest' results)) =
                  foldMap (\r-> q (len + len') (effects <* r) rest') results

instance (Applicative m, Traversable m, Ord s) => CommittedParsing (ParserT m g s) where
   type CommittedResults (ParserT m g s) = ParseResults s
   commit (Parser p) = Parser q
      where q rest = case p rest
                     of ResultList [] failure -> ResultList [ResultsOfLengthT
                                                             $ ROL 0 rest (pure (Left failure) :| [])] mempty
                        ResultList rl failure -> ResultList (mapResults (fmap Right) <$> rl) failure
   admit (Parser p) = Parser q
      where q rest = case p rest
                     of ResultList [] failure -> ResultList [] failure
                        ResultList rl failure -> foldMap expose rl <> ResultList [] failure
            expose (ResultsOfLengthT (ROL len t rs)) = case nonEmpty successes of
               Nothing -> ResultList [] (mconcat failures)
               Just successes' -> ResultList [ResultsOfLengthT $ ROL len t successes'] (mconcat failures)
               where (failures, successes) = partitionEithers (sequenceA <$> toList rs)

instance (Applicative m, MonoidNull s, Ord s) => LookAheadParsing (ParserT m g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind _ rl@(ResultList [] _) = rl
            rewind t (ResultList rl failure) =
               ResultList [ResultsOfLengthT $ ROL 0 t $ foldr1 (<>) (results <$> rl)] failure
            results (ResultsOfLengthT (ROL _ _ r)) = r

instance (Applicative m, Ord s, Show s, TextualMonoid s) => CharParsing (ParserT m g s) where
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.characterPrefix s
               of Just first | predicate first -> singleResult 1 t first
                  _ -> ResultList mempty (expected (Down $ length rest) "Char.satisfy")
            p [] = ResultList mempty (expected 0 "Char.satisfy")
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Applicative m, Eq (m ()), Ord s) => AmbiguousParsing (ParserT m g s) where
   ambiguous (Parser p) = Parser q
      where q rest | ResultList rs failure <- p rest = ResultList (groupByLength <$> rs) failure
            groupByLength :: ResultsOfLengthT m g s r -> ResultsOfLengthT m g s (Ambiguous r)
            groupByLength (ResultsOfLengthT (ROL l rest rs)) =
               ResultsOfLengthT (ROL l rest $ (Ambiguous <$>) <$> fromList (sequenceA <$> groupBy ((==) `on` void) rs))

-- | Turns a context-free parser into a backtracking PEG parser that consumes the longest possible prefix of the list
-- of input tails, opposite of 'peg'
longest :: ParserT Identity g s a -> Backtrack.Parser g [(s, g (ResultListT Identity g s))] a
longest p = Backtrack.Parser q where
   q rest = case applyParser p rest
            of ResultList [] (ParseFailure pos positive negative)
                  -> Backtrack.NoParse (ParseFailure pos (map message positive) (map message negative))
               ResultList rs _ -> parsed (last rs)
   parsed (ResultsOfLengthT (ROL l s (Identity r:|_))) = Backtrack.Parsed l r s
   message (StaticDescription msg) = StaticDescription msg
   message (LiteralDescription s) = LiteralDescription [(s, error "longest")]

-- | Turns a backtracking PEG parser of the list of input tails into a context-free parser, opposite of 'longest'
peg :: (Applicative m, Ord s) => Backtrack.Parser g [(s, g (ResultListT m g s))] a -> ParserT m g s a
peg p = Parser q where
   q rest = case Backtrack.applyParser p rest
            of Backtrack.Parsed l result suffix -> singleResult l suffix result
               Backtrack.NoParse (ParseFailure pos positive negative) ->
                  ResultList mempty (ParseFailure pos ((fst . head <$>) <$> positive) ((fst . head <$>) <$> negative))

-- | Turns a backtracking PEG parser into a context-free parser
terminalPEG :: (Applicative m, Monoid s, Ord s) => Backtrack.Parser g s a -> ParserT m g s a
terminalPEG p = Parser q where
   q [] = case Backtrack.applyParser p mempty
            of Backtrack.Parsed l result _ -> singleResult l [] result
               Backtrack.NoParse failure -> ResultList mempty failure
   q rest@((s, _):_) = case Backtrack.applyParser p s
                       of Backtrack.Parsed l result _ -> singleResult l (drop l rest) result
                          Backtrack.NoParse failure -> ResultList mempty failure

fromResultList :: (Functor m, Eq s, FactorialMonoid s) => ResultListT m g s r -> ParseResults s [(s, m r)]
fromResultList (ResultList [] (ParseFailure pos positive negative)) = Left (ParseFailure (pos - 1) positive negative)
fromResultList (ResultList rl _failure) = Right (foldMap f rl)
   where f (ResultsOfLengthT (ROL _ ((s, _):_) r)) = (,) s <$> toList r
         f (ResultsOfLengthT (ROL _ [] r)) = (,) mempty <$> toList r
{-# INLINABLE fromResultList #-}

instance Functor (ResultsOfLength m g s) where
   fmap f (ROL l t a) = ROL l t (f <$> a)
   {-# INLINE fmap #-}

instance Functor m => Functor (ResultsOfLengthT m g s) where
   fmap f (ResultsOfLengthT rol) = ResultsOfLengthT (fmap f <$> rol)
   {-# INLINE fmap #-}

instance Functor m => Functor (ResultListT m g s) where
   fmap f (ResultList l failure) = ResultList ((f <$>) <$> l) failure
   {-# INLINE fmap #-}

instance (Applicative m, Ord s) => Applicative (ResultsOfLength m g s) where
   pure = ROL 0 mempty . pure
   ROL l1 _ fs <*> ROL l2 t2 xs = ROL (l1 + l2) t2 (fs <*> xs)
   {-# INLINE pure #-}
   {-# INLINE (<*>) #-}

instance (Applicative m, Ord s) => Applicative (ResultsOfLengthT m g s) where
   pure = ResultsOfLengthT . pure . pure
   ResultsOfLengthT rol1 <*> ResultsOfLengthT rol2 = ResultsOfLengthT (liftA2 (<*>) rol1 rol2)

instance (Applicative m, Ord s) => Applicative (ResultListT m g s) where
   pure a = ResultList [pure a] mempty
   ResultList rl1 f1 <*> ResultList rl2 f2 = ResultList ((<*>) <$> rl1 <*> rl2) (f1 <> f2)

instance (Applicative m, Ord s) => Alternative (ResultListT m g s) where
   empty = ResultList mempty mempty
   (<|>) = (<>)

instance (Applicative m, Ord s) => AmbiguousAlternative (ResultListT m g s) where
   ambiguousOr (ResultList rl1 f1) (ResultList rl2 f2) = ResultList (merge rl1 rl2) (f1 <> f2)
      where merge [] rl = rl
            merge rl [] = rl
            merge rl1'@(rol1@(ResultsOfLengthT (ROL l1 s1 r1)) : rest1)
                  rl2'@(rol2@(ResultsOfLengthT (ROL l2 _ r2)) : rest2)
               | l1 < l2 = rol1 : merge rest1 rl2'
               | l1 > l2 = rol2 : merge rl1' rest2
               | otherwise = ResultsOfLengthT (ROL l1 s1 $ liftA2 (liftA2 collect) r1 r2) : merge rest1 rest2
            collect (Ambiguous xs) (Ambiguous ys) = Ambiguous (xs <> ys)

instance Traversable m => Filterable (ResultListT m g s) where
   mapMaybe :: forall a b. (a -> Maybe b) -> ResultListT m g s a -> ResultListT m g s b
   mapMaybe f (ResultList rs failure) = ResultList (mapMaybe filterResults rs) failure
      where filterResults :: ResultsOfLengthT m g s a -> Maybe (ResultsOfLengthT m g s b)
            filterResults (ResultsOfLengthT (ROL l t as)) =
               ResultsOfLengthT . ROL l t <$> nonEmpty (mapMaybe (traverse f) $ toList as)

instance {-# overlaps #-} (Monad m, Traversable m, Monoid state) => Filterable (ResultListT (StateT state m) g s) where
   mapMaybe :: forall a b. (a -> Maybe b) -> ResultListT (StateT state m) g s a -> ResultListT (StateT state m) g s b
   mapMaybe f (ResultList rs failure) = ResultList (mapMaybe filterResults rs) failure
      where filterResults :: ResultsOfLengthT (StateT state m) g s a -> Maybe (ResultsOfLengthT (StateT state m) g s b)
            filterResults (ResultsOfLengthT (ROL l t as)) =
               ResultsOfLengthT . ROL l t <$> nonEmpty (mapMaybe traverseWithMonoid $ toList as)
            traverseWithMonoid :: StateT state m a -> Maybe (StateT state m b)
            traverseWithMonoid m = Trans.lift <$> traverse f (evalStateT m mempty)

instance Ord s => Semigroup (ResultListT m g s r) where
   ResultList rl1 f1 <> ResultList rl2 f2 = ResultList (merge rl1 rl2) (f1 <> f2)
      where merge [] rl = rl
            merge rl [] = rl
            merge rl1'@(rol1@(ResultsOfLengthT (ROL l1 s1 r1)) : rest1)
                 rl2'@(rol2@(ResultsOfLengthT (ROL l2 _ r2)) : rest2)
               | l1 < l2 = rol1 : merge rest1 rl2'
               | l1 > l2 = rol2 : merge rl1' rest2
               | otherwise = ResultsOfLengthT (ROL l1 s1 (r1 <> r2)) : merge rest1 rest2

instance Ord s => Monoid (ResultListT m g s r) where
   mempty = ResultList mempty mempty
   mappend = (<>)

instance FallibleResults (ResultListT m g) where
   hasSuccess (ResultList [] _) = False
   hasSuccess _ = True
   failureOf (ResultList _ failure) = failure
   failWith = ResultList []
