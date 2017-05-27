{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, InstanceSigs,
             RankNTypes, ScopedTypeVariables, TypeFamilies #-}
module Text.Grampa.ContextFree.Memoizing (FailureInfo(..), ResultList(..), Parser(..), fromResultList, reparseTails)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
import Data.Char (isSpace)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.List (genericLength, nub)
import Data.Monoid (Monoid(mappend, mempty), (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid (isPrefixOf))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(length, splitPrimePrefix))
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.String (fromString)
import Data.Word (Word64)

import qualified Text.Parser.Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))
import Text.Parser.Token (TokenParsing(someSpace))

import qualified Rank2

import Text.Grampa.Class (GrammarParsing(..), MonoidParsing(..), MultiParsing(..), ParseResults, ParseFailure(..))

import Prelude hiding (iterate, length, null, showList, span, takeWhile)

-- | Parser for a context-free grammar with packrat-like sharing of parse results. It does not support left-recursive
-- grammars.
newtype Parser g s r = Parser{applyParser :: [(s, g (ResultList g s))] -> ResultList g s r}
            
data ResultList g s r = ResultList ![ResultInfo g s r] {-# UNPACK #-} !FailureInfo
data ResultInfo g s r = ResultInfo ![(s, g (ResultList g s))] !r
data FailureInfo = FailureInfo !Int Word64 [String] deriving (Eq, Show)

instance (Show s, Show r) => Show (ResultList g s r) where
   show (ResultList l f) = "ResultList (" ++ shows l (") (" ++ shows f ")")

instance Show1 (ResultList g s) where
   liftShowsPrec _sp showList _prec (ResultList l f) rest = "ResultList " ++ showList (simplify <$> l) (shows f rest)
      where simplify (ResultInfo _ r) = r

instance (Show s, Show r) => Show (ResultInfo g s r) where
   show (ResultInfo t r) = "(ResultInfo @" ++ show (fst $ head t) ++ " " ++ shows r ")"

instance Functor (ResultInfo g s) where
   fmap f (ResultInfo t r) = ResultInfo t (f r)

instance Functor (ResultList g s) where
   fmap f (ResultList l failure) = ResultList ((f <$>) <$> l) failure

instance Monoid (ResultList g s r) where
   mempty = ResultList [] mempty
   ResultList rl1 f1 `mappend` ResultList rl2 f2 = ResultList (rl1 <> rl2) (f1 <> f2)

instance Monoid FailureInfo where
   mempty = FailureInfo 0 maxBound []
   f1@(FailureInfo s1 pos1 exp1) `mappend` f2@(FailureInfo s2 pos2 exp2)
      | s1 < s2 = f2
      | s1 > s2 = f1
      | otherwise = FailureInfo s1 pos' exp'
      where (pos', exp') | pos1 < pos2 = (pos1, exp1)
                         | pos1 > pos2 = (pos2, exp2)
                         | otherwise = (pos1, exp1 <> exp2)

instance Functor (Parser g i) where
   fmap f (Parser p) = Parser (fmap f . p)

instance Applicative (Parser g i) where
   pure a = Parser (\rest-> ResultList [ResultInfo rest a] mempty)
   Parser p <*> Parser q = Parser r where
      r rest = case p rest
               of ResultList results failure -> ResultList [] failure <> foldMap continue results
      continue (ResultInfo rest' f) = f <$> q rest'


instance Alternative (Parser g i) where
   empty = Parser (\rest-> ResultList [] $ FailureInfo 0 (genericLength rest) ["empty"])
   Parser p <|> Parser q = Parser r where
      r rest = p rest <> q rest

instance Monad (Parser g i) where
   return = pure
   Parser p >>= f = Parser q where
      q rest = case p rest
               of ResultList results failure -> ResultList [] failure <> foldMap continue results
      continue (ResultInfo rest' a) = applyParser (f a) rest'

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance GrammarParsing Parser where
   type GrammarFunctor Parser = ResultList
   nonTerminal f = Parser p where
      p ((_, d) : _) = f d
      p _ = ResultList [] (FailureInfo 1 0 ["NonTerminal at endOfInput"])

-- | Memoizing parser guarantees O(n²) performance, but provides no left recursion support.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Functor' g, 'FactorialMonoid' s) =>
--                  g (Memoizing.'Parser' g s) -> s -> g ('Compose' 'ParseResults' [])
-- @
instance MultiParsing Parser where
   type ResultFunctor Parser = Compose ParseResults []
   -- | Returns the list of all possible input prefix parses paired with the remaining input suffix.
   parsePrefix g input = Rank2.fmap (Compose . Compose . fromResultList input) (snd $ head $ parseTails g input)
   parseComplete :: forall g s. (Rank2.Functor g, FactorialMonoid s) =>
                    g (Parser g s) -> s -> g (Compose ParseResults [])
   parseComplete g input = Rank2.fmap ((snd <$>) . Compose . fromResultList input)
                              (snd $ head $ reparseTails close $ parseTails g input)
      where close = Rank2.fmap (<* endOfInput) g

parseTails :: (Rank2.Functor g, FactorialMonoid s) => g (Parser g s) -> s -> [(s, g (ResultList g s))]
parseTails g input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d):parsedTail
                  d      = Rank2.fmap (($ parsed) . applyParser) g

reparseTails :: Rank2.Functor g => g (Parser g s) -> [(s, g (ResultList g s))] -> [(s, g (ResultList g s))]
reparseTails _ [] = []
reparseTails final parsed@((s, _):_) = (s, gd):parsed
   where gd = Rank2.fmap (`applyParser` parsed) final

instance MonoidParsing (Parser g) where
   endOfInput = eof
   getInput = Parser p
      where p rest@((s, _):_) = ResultList [ResultInfo [last rest] s] mempty
            p [] = ResultList [ResultInfo [] mempty] mempty
   anyToken = Parser p
      where p rest@((s, _):t) = case splitPrimePrefix s
                                of Just (first, _) -> ResultList [ResultInfo t first] mempty
                                   _ -> ResultList [] (FailureInfo 1 (genericLength rest) ["anyToken"])
            p [] = ResultList [] (FailureInfo 1 0 ["anyToken"])
   satisfy predicate = Parser p
      where p rest@((s, _):t) =
               case splitPrimePrefix s
               of Just (first, _) | predicate first -> ResultList [ResultInfo t first] mempty
                  _ -> ResultList [] (FailureInfo 1 (genericLength rest) ["satisfy"])
            p [] = ResultList [] (FailureInfo 1 0 ["satisfy"])
   satisfyChar predicate = Parser p
      where p rest@((s, _):t) =
               case Textual.splitCharacterPrefix s
               of Just (first, _) | predicate first -> ResultList [ResultInfo t first] mempty
                  _ -> ResultList [] (FailureInfo 1 (genericLength rest) ["satisfyChar"])
            p [] = ResultList [] (FailureInfo 1 0 ["satisfyChar"])
   scan s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = ResultList [ResultInfo (drop (Factorial.length prefix) rest) prefix] mempty
               where (prefix, _, _) = Factorial.spanMaybe' s f i
            p _ [] = ResultList [ResultInfo [] mempty] mempty
   scanChars s0 f = Parser (p s0)
      where p s rest@((i, _) : _) = ResultList [ResultInfo (drop (Factorial.length prefix) rest) prefix] mempty
               where (prefix, _, _) = Textual.spanMaybe_' s f i
            p _ [] = ResultList [ResultInfo [] mempty] mempty
   takeWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s =
                    ResultList [ResultInfo (drop (Factorial.length x) rest) x] mempty
            p [] = ResultList [ResultInfo [] mempty] mempty
   takeWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Factorial.takeWhile predicate s, not (null x) =
                    ResultList [ResultInfo (drop (Factorial.length x) rest) x] mempty
            p rest = ResultList [] (FailureInfo 1 (genericLength rest) ["takeWhile1"])
   takeCharsWhile predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s =
                    ResultList [ResultInfo (drop (Factorial.length x) rest) x] mempty
            p [] = ResultList [ResultInfo [] mempty] mempty
   takeCharsWhile1 predicate = Parser p
      where p rest@((s, _) : _)
               | x <- Textual.takeWhile_ False predicate s, not (null x) =
                    ResultList [ResultInfo (drop (Factorial.length x) rest) x] mempty
            p rest = ResultList [] (FailureInfo 1 (genericLength rest) ["takeCharsWhile1"])
   string s = Parser p where
      p rest@((s', _) : _)
         | s `isPrefixOf` s' = ResultList [ResultInfo (Factorial.drop (Factorial.length s) rest) s] mempty
      p rest = ResultList [] (FailureInfo 1 (genericLength rest) ["string " ++ show s])
   whiteSpace = () <$ takeCharsWhile isSpace
   concatMany p = go
      where go = mempty <|> (<>) <$> p <*> go

instance MonoidNull s => Parsing (Parser g s) where
   try (Parser p) = Parser (weakenResults . p)
      where weakenResults (ResultList rl (FailureInfo s pos msgs)) = ResultList rl (FailureInfo (pred s) pos msgs)
   Parser p <?> msg  = Parser (strengthenResults . p)
      where strengthenResults (ResultList rl (FailureInfo s pos _msgs)) = ResultList rl (FailureInfo (succ s) pos [msg])
   notFollowedBy (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList [] _) = ResultList [ResultInfo t ()] mempty
            rewind t ResultList{} = ResultList [] (FailureInfo 1 (genericLength t) ["notFollowedBy"])
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = Parser (\t-> ResultList [] $ FailureInfo 0 (genericLength t) [msg])
   eof = Parser f
      where f rest@((s, _):_)
               | null s = ResultList [ResultInfo rest ()] mempty
               | otherwise = ResultList [] (FailureInfo 1 (genericLength rest) ["endOfInput"])
            f [] = ResultList [ResultInfo [] ()] mempty

instance MonoidNull s => LookAheadParsing (Parser g s) where
   lookAhead (Parser p) = Parser (\input-> rewind input (p input))
      where rewind t (ResultList rl failure) = ResultList (rewindInput t <$> rl) failure
            rewindInput t (ResultInfo _ r) = ResultInfo t r

instance (Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Show s, TextualMonoid s) => TokenParsing (Parser g s) where
   someSpace = () <$ takeCharsWhile1 isSpace

fromResultList :: FactorialMonoid s => s -> ResultList g s r -> ParseResults [(s, r)]
fromResultList s (ResultList [] (FailureInfo _ pos msgs)) =
   Left (ParseFailure (length s - fromIntegral pos + 1) (nub msgs))
fromResultList _ (ResultList rl _failure) = Right (f <$> rl)
   where f (ResultInfo ((s, _):_) r) = (s, r)
         f (ResultInfo [] r) = (mempty, r)
