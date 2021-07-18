{-# LANGUAGE CPP, FlexibleContexts, InstanceSigs, GeneralizedNewtypeDeriving,
             RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
module Text.Grampa.ContextFree.Parallel (FailureInfo(..), ResultList(..), Parser, fromResultList)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
#if MIN_VERSION_base(4,13,0)
import Control.Monad (MonadFail(fail))
#endif
import Data.Foldable (toList)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (nub)
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

import qualified Rank2

import Text.Grampa.Class (DeterministicParsing(..), InputParsing(..), InputCharParsing(..), MultiParsing(..),
                          ParseResults, ParseFailure(..), Expected(..))
import Text.Grampa.Internal (BinTree(..), FailureInfo(..), noFailure, TraceableParsing(..))

import Prelude hiding (iterate, null, showList, span, takeWhile)

-- | Parser type for context-free grammars using a parallel parsing algorithm with no result sharing nor left recursion
-- support.
newtype Parser (g :: (* -> *) -> *) s r = Parser{applyParser :: s -> ResultList s r}

data ResultList s r = ResultList !(BinTree (ResultInfo s r)) {-# UNPACK #-} !(FailureInfo s)
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

instance Semigroup (ResultList s r) where
   ResultList rl1 f1 <> ResultList rl2 f2 = ResultList (rl1 <> rl2) (f1 <> f2)

instance Monoid (ResultList s r) where
   mempty = ResultList mempty noFailure
   mappend = (<>)

instance Functor (Parser g s) where
   fmap f (Parser p) = Parser (fmap f . p)

instance Applicative (Parser g s) where
   pure a = Parser (\rest-> ResultList (Leaf $ ResultInfo rest a) noFailure)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultInfo rest' f) = f <$> q rest'


instance FactorialMonoid s => Alternative (Parser g s) where
   empty = Parser (\s-> ResultList mempty $ FailureInfo (Factorial.length s) [Expected "empty"])
   Parser p <|> Parser q = Parser r where
      r rest = p rest <> q rest

instance FactorialMonoid s => Filterable (Parser g s) where
   mapMaybe f (Parser p) = Parser (mapMaybe f . p)

#if MIN_VERSION_base(4,13,0)
instance Monad (Parser g s) where
#else
instance Factorial.FactorialMonoid s => Monad (Parser g s) where
#endif
   return = pure
   Parser p >>= f = Parser q where
      q rest = case p rest
               of ResultList results failure -> ResultList mempty failure <> foldMap continue results
      continue (ResultInfo rest' a) = applyParser (f a) rest'

#if MIN_VERSION_base(4,13,0)
instance FactorialMonoid s => MonadFail (Parser g s) where
#endif
   fail msg = Parser (\s-> ResultList mempty $ FailureInfo (Factorial.length s) [Expected msg])

instance FactorialMonoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Semigroup x => Semigroup (Parser g s x) where
   (<>) = liftA2 (<>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

-- | Parallel parser produces a list of all possible parses.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, Eq s, 'FactorialMonoid' s) =>
--                  g (Parallel.'Parser' g s) -> s -> g ('Compose' ('ParseResults' s) [])
-- @
instance (Cancellative.LeftReductive s, FactorialMonoid s) => MultiParsing (Parser g s) where
   type ResultFunctor (Parser g s) = Compose (ParseResults s) []
   -- | Returns the list of all possible input prefix parses paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . Compose . fromResultList input . (`applyParser` input)) g
   -- | Returns the list of all possible parses of complete input.
   parseComplete :: (Rank2.Functor g', Eq s, FactorialMonoid s) =>
                    g' (Parser g s) -> s -> g' (Compose (ParseResults s) [])
   parseComplete g input = Rank2.fmap ((snd <$>) . getCompose) (parsePrefix (Rank2.fmap (<* eof) g) input)

instance (Cancellative.LeftReductive s, FactorialMonoid s) => InputParsing (Parser g s) where
   type ParserInput (Parser g s) = s
   getInput = Parser p
      where p s = ResultList (Leaf $ ResultInfo s s) noFailure
   anyToken = Parser p
      where p s = case Factorial.splitPrimePrefix s
                  of Just (first, rest) -> ResultList (Leaf $ ResultInfo rest first) noFailure
                     _ -> ResultList mempty (FailureInfo (Factorial.length s) [Expected "anyToken"])
   satisfy predicate = Parser p
      where p s = case Factorial.splitPrimePrefix s
                  of Just (first, rest) | predicate first -> ResultList (Leaf $ ResultInfo rest first) noFailure
                     _ -> ResultList mempty (FailureInfo (Factorial.length s) [Expected "satisfy"])
   notSatisfy predicate = Parser p
      where p s = case Factorial.splitPrimePrefix s
                  of Just (first, _) 
                        | predicate first -> ResultList mempty (FailureInfo (Factorial.length s) [Expected "notSatisfy"])
                     _ -> ResultList (Leaf $ ResultInfo s ()) noFailure
   scan s0 f = Parser (p s0)
      where p s i = ResultList (Leaf $ ResultInfo suffix prefix) noFailure
               where (prefix, suffix, _) = Factorial.spanMaybe' s f i
   take n = Parser p
      where p s
              | (prefix, suffix) <- Factorial.splitAt n s,
                Factorial.length prefix == n = ResultList (Leaf $ ResultInfo suffix prefix) noFailure
              | otherwise = ResultList mempty (FailureInfo (Factorial.length s) [Expected $ "take " ++ show n])
   takeWhile predicate = Parser p
      where p s = ResultList (Leaf $ ResultInfo suffix prefix) noFailure
              where (prefix, suffix) = Factorial.span predicate s
   takeWhile1 predicate = Parser p
      where p s | (prefix, suffix) <- Factorial.span predicate s = 
               if Null.null prefix
               then ResultList mempty (FailureInfo (Factorial.length s) [Expected "takeWhile1"])
               else ResultList (Leaf $ ResultInfo suffix prefix) noFailure
   string s = Parser p where
      p s' | Just suffix <- Cancellative.stripPrefix s s' = ResultList (Leaf $ ResultInfo suffix s) noFailure
           | otherwise = ResultList mempty (FailureInfo (Factorial.length s') [ExpectedInput s])

instance InputParsing (Parser g s)  => TraceableParsing (Parser g s) where
   traceInput description (Parser p) = Parser q
      where q s = case traceWith "Parsing " (p s)
                  of rl@(ResultList EmptyTree _) -> traceWith "Failed " rl
                     rl -> traceWith "Parsed " rl
               where traceWith prefix = trace (prefix <> description s)

instance TextualMonoid s => InputCharParsing (Parser g s) where
   satisfyCharInput predicate = Parser p
      where p s =
               case Textual.splitCharacterPrefix s
               of Just (first, rest)
                     | predicate first -> ResultList (Leaf $ ResultInfo rest $ Factorial.primePrefix s) noFailure
                  _ -> ResultList mempty (FailureInfo (Factorial.length s) [Expected "satisfyCharInput"])
   notSatisfyChar predicate = Parser p
      where p s = case Textual.characterPrefix s
                  of Just first 
                        | predicate first -> ResultList mempty (FailureInfo (Factorial.length s) [Expected "notSatisfyChar"])
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
               then ResultList mempty (FailureInfo (Factorial.length s) [Expected "takeCharsWhile1"])
               else ResultList (Leaf $ ResultInfo suffix prefix) noFailure

instance FactorialMonoid s => Parsing (Parser g s) where
   try (Parser p) = Parser q
      where q rest = rewindFailure (p rest)
               where rewindFailure (ResultList rl (FailureInfo _pos _msgs)) =
                        ResultList rl (FailureInfo (Factorial.length rest) [])
   Parser p <?> msg  = Parser q
      where q rest = replaceFailure (p rest)
               where replaceFailure (ResultList EmptyTree (FailureInfo pos msgs)) =
                        ResultList EmptyTree (FailureInfo pos $
                                              if pos == Factorial.length rest then [Expected msg] else msgs)
                     replaceFailure rl = rl
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList EmptyTree _) = ResultList (Leaf $ ResultInfo t ()) noFailure
            rewind t ResultList{} = ResultList mempty (FailureInfo (Factorial.length t) [Expected "notFollowedBy"])
   skipMany p = go
      where go = pure () <|> try p *> go
   unexpected msg = Parser (\t-> ResultList mempty $ FailureInfo (Factorial.length t) [Expected msg])
   eof = Parser f
      where f s | null s = ResultList (Leaf $ ResultInfo s ()) noFailure
                | otherwise = ResultList mempty (FailureInfo (Factorial.length s) [Expected "end of input"])

instance FactorialMonoid s => DeterministicParsing (Parser g s) where
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

instance FactorialMonoid s => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList rl failure) = ResultList (rewindInput t <$> rl) failure
            rewindInput t (ResultInfo _ r) = ResultInfo t r

instance TextualMonoid s => CharParsing (Parser g s) where
   satisfy predicate = Parser p
      where p s =
               case Textual.splitCharacterPrefix s
               of Just (first, rest) | predicate first -> ResultList (Leaf $ ResultInfo rest first) noFailure
                  _ -> ResultList mempty (FailureInfo (Factorial.length s) [Expected "Char.satisfy"])
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

fromResultList :: (Eq s, FactorialMonoid s) => s -> ResultList s r -> ParseResults s [(s, r)]
fromResultList s (ResultList EmptyTree (FailureInfo pos msgs)) = Left (ParseFailure (fromIntegral pos) (nub msgs))
fromResultList _ (ResultList rl _failure) = Right (f <$> toList rl)
   where f (ResultInfo s r) = (s, r)
