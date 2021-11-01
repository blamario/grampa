{-# LANGUAGE CPP, FlexibleContexts, InstanceSigs, GeneralizedNewtypeDeriving,
             RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Text.Grampa.ContextFree.Parallel (ResultList(..), Parser)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
#if MIN_VERSION_base(4,13,0)
import Control.Monad (MonadFail(fail))
#endif
import Data.Foldable (toList)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.Semigroup (Semigroup(..))
import qualified Data.Semigroup.Cancellative as Cancellative
import Data.Monoid (Monoid(mappend, mempty))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Null as Null
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.String (fromString)
import Debug.Trace (trace)
import Witherable (Filterable(mapMaybe))

import qualified Text.Parser.Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))
import Text.Parser.Input.Position (fromEnd)

import qualified Rank2

import Text.Grampa.Class (CommittedParsing(..), DeterministicParsing(..),
                          InputParsing(..), InputCharParsing(..), MultiParsing(..),
                          ParseResults, ParseFailure(..), FailureDescription(..), Pos)
import Text.Grampa.Internal (BinTree(..), expected, noFailure, TraceableParsing(..))

import Prelude hiding (iterate, null, showList, span, takeWhile)

-- | Parser type for context-free grammars using a parallel parsing algorithm with no result sharing nor left recursion
-- support.
newtype Parser (g :: (* -> *) -> *) s r = Parser{applyParser :: s -> ResultList s r}

data ResultList s r = ResultList !(BinTree (ResultInfo s r)) {-# UNPACK #-} !(ParseFailure Pos s)
data ResultInfo s r = ResultInfo !s !r

instance (Show s, Show r) => Show (ResultList s r) where
   show (ResultList l f) = "ResultList (" ++ shows l (") (" ++ shows f ")")

instance Show s => Show1 (ResultList s) where
   liftShowsPrec _sp showList _prec (ResultList l f) rest = "ResultList " ++ showList (simplify <$> toList l) (shows f rest)
      where simplify (ResultInfo _ r) = r

instance (Show s, Show r) => Show (ResultInfo s r) where
   show (ResultInfo s r) = "(ResultInfo @" ++ show s ++ " " ++ shows r ")"

instance Functor (ResultInfo s) where
   fmap f (ResultInfo s r) = ResultInfo s (f r)

instance Foldable (ResultInfo s) where
   foldMap f (ResultInfo _ r) = f r

instance Traversable (ResultInfo s) where
   traverse f (ResultInfo s r) = ResultInfo s <$> f r

instance Filterable (ResultList s) where
   mapMaybe f (ResultList l failure) = ResultList (mapMaybe (traverse f) l) failure

instance Functor (ResultList s) where
   fmap f (ResultList l failure) = ResultList ((f <$>) <$> l) failure

instance Ord s => Semigroup (ResultList s r) where
   ResultList rl1 f1 <> ResultList rl2 f2 = ResultList (rl1 <> rl2) (f1 <> f2)

instance Ord s => Monoid (ResultList s r) where
   mempty = ResultList mempty noFailure
   mappend = (<>)

instance Functor (Parser g s) where
   fmap f (Parser p) = Parser (fmap f . p)

instance Ord s => Applicative (Parser g s) where
   pure a = Parser (\rest-> ResultList (Leaf $ ResultInfo rest a) noFailure)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultInfo rest' f) = f <$> q rest'


instance (FactorialMonoid s, Ord s) => Alternative (Parser g s) where
   empty = Parser (\s-> ResultList mempty $ ParseFailure (fromEnd $ Factorial.length s) [] [])
   Parser p <|> Parser q = Parser r where
      r rest = p rest <> q rest

instance FactorialMonoid s => Filterable (Parser g s) where
   mapMaybe f (Parser p) = Parser (mapMaybe f . p)

#if MIN_VERSION_base(4,13,0)
instance Ord s => Monad (Parser g s) where
#else
instance (Factorial.FactorialMonoid s, Ord s) => Monad (Parser g s) where
#endif
   return = pure
   Parser p >>= f = Parser q where
      q rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultInfo rest' a) = applyParser (f a) rest'

#if MIN_VERSION_base(4,13,0)
instance (FactorialMonoid s, Ord s) => MonadFail (Parser g s) where
#endif
   fail msg = Parser (\s-> ResultList mempty $ ParseFailure (fromEnd $ Factorial.length s) [] [StaticDescription msg])

instance (FactorialMonoid s, Ord s) => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance (Ord s, Semigroup x) => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance (Monoid x, Ord s) => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

-- | Parallel parser produces a list of all possible parses.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, Eq s, 'FactorialMonoid' s) =>
--                  g (Parallel.'Parser' g s) -> s -> g ('Compose' ('ParseResults' s) [])
-- @
instance (Cancellative.LeftReductive s, FactorialMonoid s, Ord s) => MultiParsing (Parser g s) where
   type ResultFunctor (Parser g s) = Compose (ParseResults s) []
   -- | Returns the list of all possible input prefix parses paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . Compose . fromResultList . (`applyParser` input)) g
   -- | Returns the list of all possible parses of complete input.
   parseComplete :: (Rank2.Functor g', Eq s, FactorialMonoid s) =>
                    g' (Parser g s) -> s -> g' (Compose (ParseResults s) [])
   parseComplete g input = Rank2.fmap ((snd <$>) . getCompose) (parsePrefix (Rank2.fmap (<* eof) g) input)

instance (Cancellative.LeftReductive s, FactorialMonoid s, Ord s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   getInput = Parser p
      where p s = ResultList (Leaf $ ResultInfo s s) noFailure
   anyToken = Parser p
      where p s = case Factorial.splitPrimePrefix s
                  of Just (first, rest) -> ResultList (Leaf $ ResultInfo rest first) noFailure
                     _ -> ResultList mempty (expected (fromEnd $ Factorial.length s) "anyToken")
   satisfy predicate = Parser p
      where p s = case Factorial.splitPrimePrefix s
                  of Just (first, rest) | predicate first -> ResultList (Leaf $ ResultInfo rest first) noFailure
                     _ -> ResultList mempty (expected (fromEnd $ Factorial.length s) "satisfy")
   notSatisfy predicate = Parser p
      where p s = case Factorial.splitPrimePrefix s
                  of Just (first, _) 
                        | predicate first -> ResultList mempty (expected (fromEnd $ Factorial.length s) "notSatisfy")
                     _ -> ResultList (Leaf $ ResultInfo s ()) noFailure
   scan s0 f = Parser (p s0)
      where p s i = ResultList (Leaf $ ResultInfo suffix prefix) noFailure
               where (prefix, suffix, _) = Factorial.spanMaybe' s f i
   take n = Parser p
      where p s
              | (prefix, suffix) <- Factorial.splitAt n s,
                Factorial.length prefix == n = ResultList (Leaf $ ResultInfo suffix prefix) noFailure
              | otherwise = ResultList mempty (expected (fromEnd $ Factorial.length s) $ "take " ++ show n)
   takeWhile predicate = Parser p
      where p s = ResultList (Leaf $ ResultInfo suffix prefix) noFailure
              where (prefix, suffix) = Factorial.span predicate s
   takeWhile1 predicate = Parser p
      where p s | (prefix, suffix) <- Factorial.span predicate s = 
               if Null.null prefix
               then ResultList mempty (expected (fromEnd $ Factorial.length s) "takeWhile1")
               else ResultList (Leaf $ ResultInfo suffix prefix) noFailure
   string s = Parser p where
      p s' | Just suffix <- Cancellative.stripPrefix s s' = ResultList (Leaf $ ResultInfo suffix s) noFailure
           | otherwise = ResultList mempty (ParseFailure (fromEnd $ Factorial.length s') [LiteralDescription s] [])

instance InputParsing (Parser g s)  => TraceableParsing (Parser g s) where
   traceInput description (Parser p) = Parser q
      where q s = case traceWith "Parsing " (p s)
                  of rl@(ResultList EmptyTree _) -> traceWith "Failed " rl
                     rl -> traceWith "Parsed " rl
               where traceWith prefix = trace (prefix <> description s)

instance (Ord s, TextualMonoid s) => InputCharParsing (Parser g s) where
   satisfyCharInput predicate = Parser p
      where p s =
               case Textual.splitCharacterPrefix s
               of Just (first, rest)
                     | predicate first -> ResultList (Leaf $ ResultInfo rest $ Factorial.primePrefix s) noFailure
                  _ -> ResultList mempty (expected (fromEnd $ Factorial.length s) "satisfyCharInput")
   notSatisfyChar predicate = Parser p
      where p s = case Textual.characterPrefix s
                  of Just first | predicate first
                        -> ResultList mempty (expected (fromEnd $ Factorial.length s) "notSatisfyChar")
                     _ -> ResultList (Leaf $ ResultInfo s ()) noFailure
   scanChars s0 f = Parser (p s0)
      where p s i = ResultList (Leaf $ ResultInfo suffix prefix) noFailure
               where (prefix, suffix, _) = Textual.spanMaybe_' s f i
   takeCharsWhile predicate = Parser p
      where p s | (prefix, suffix) <- Textual.span_ False predicate s = 
               ResultList (Leaf $ ResultInfo suffix prefix) noFailure
   takeCharsWhile1 predicate = Parser p
      where p s | (prefix, suffix) <- Textual.span_ False predicate s =
               if null prefix
               then ResultList mempty (expected (fromEnd $ Factorial.length s) "takeCharsWhile1")
               else ResultList (Leaf $ ResultInfo suffix prefix) noFailure

instance (FactorialMonoid s, Ord s) => Parsing (Parser g s) where
   try (Parser p) = Parser q
      where q rest = rewindFailure (p rest)
               where rewindFailure (ResultList rl _) =
                        ResultList rl (ParseFailure (fromEnd $ Factorial.length rest) [] [])
   Parser p <?> msg  = Parser q
      where q rest = replaceFailure (p rest)
               where replaceFailure (ResultList EmptyTree (ParseFailure pos msgs erroneous)) =
                        ResultList EmptyTree (ParseFailure pos
                                                           (if pos == fromEnd (Factorial.length rest)
                                                            then [StaticDescription msg] else msgs)
                                                           erroneous)
                     replaceFailure rl = rl
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList EmptyTree _) = ResultList (Leaf $ ResultInfo t ()) noFailure
            rewind t ResultList{} = ResultList mempty (expected (fromEnd $ Factorial.length t) "notFollowedBy")
   skipMany p = go
      where go = pure () <|> try p *> go
   unexpected msg = Parser (\t-> ResultList mempty
                                 $ ParseFailure (fromEnd $ Factorial.length t) [] [StaticDescription msg])
   eof = Parser f
      where f s | null s = ResultList (Leaf $ ResultInfo s ()) noFailure
                | otherwise = ResultList mempty (expected (fromEnd $ Factorial.length s) "end of input")

instance (FactorialMonoid s, Ord s) => DeterministicParsing (Parser g s) where
   Parser p <<|> Parser q = Parser r where
      r rest = case p rest
               of rl@(ResultList EmptyTree _failure) -> rl <> q rest
                  rl -> rl
   takeSome p = (:) <$> p <*> takeMany p
   takeMany (Parser p) = Parser (q id) where
      q acc rest = case p rest
                   of ResultList EmptyTree _failure -> ResultList (Leaf $ ResultInfo rest (acc [])) mempty
                      ResultList rl _ -> foldMap continue rl
         where continue (ResultInfo rest' result) = q (acc . (result:)) rest'
   skipAll (Parser p) = Parser q where
      q rest = case p rest
               of ResultList EmptyTree _failure -> ResultList (Leaf $ ResultInfo rest ()) mempty
                  ResultList rl _failure -> foldMap continue rl
         where continue (ResultInfo rest' _) = q rest'

instance (FactorialMonoid s, Ord s) => CommittedParsing (Parser g s) where
   type CommittedResults (Parser g s) = ParseResults s
   commit (Parser p) = Parser q
      where q rest = case p rest
                     of ResultList EmptyTree failure -> ResultList (Leaf $ ResultInfo rest $ Left failure) mempty
                        ResultList rl failure -> ResultList (fmap Right <$> rl) failure
   admit (Parser p) = Parser q
      where q rest = case p rest
                     of ResultList EmptyTree failure -> ResultList EmptyTree failure
                        ResultList rl failure -> foldMap expose rl <> ResultList EmptyTree failure
            expose (ResultInfo _ (Left failure)) = ResultList EmptyTree failure
            expose (ResultInfo rest (Right r)) = ResultList (Leaf $ ResultInfo rest r) mempty

instance (FactorialMonoid s, Ord s) => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList rl failure) = ResultList (rewindInput t <$> rl) failure
            rewindInput t (ResultInfo _ r) = ResultInfo t r

instance (TextualMonoid s, Ord s) => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p s =
               case Textual.splitCharacterPrefix s
               of Just (first, rest) | predicate first -> ResultList (Leaf $ ResultInfo rest first) noFailure
                  _ -> ResultList mempty (expected (fromEnd $ Factorial.length s) "Char.satisfy")
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

fromResultList :: (Eq s, FactorialMonoid s) => ResultList s r -> ParseResults s [(s, r)]
fromResultList (ResultList EmptyTree failure) = Left failure
fromResultList (ResultList rl _failure) = Right (f <$> toList rl)
   where f (ResultInfo s r) = (s, r)
