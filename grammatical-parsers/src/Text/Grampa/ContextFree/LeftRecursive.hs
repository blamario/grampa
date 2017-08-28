{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, InstanceSigs,
             RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS -fno-full-laziness #-}
module Text.Grampa.ContextFree.LeftRecursive (Fixed, Parser, SeparatedParser(..), longest, peg, terminalPEG, 
                                              parseSeparated, separated)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
import Control.Monad.Trans.State.Lazy (State, evalState, get, put)

import Data.Char (isSpace)
import Data.Functor.Compose (Compose(..))
import Data.Maybe (isJust)

import Data.Monoid (Monoid(mempty), All(..), Any(..), (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.String (fromString)

import qualified Text.Parser.Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))
import Text.Parser.Token (TokenParsing(someSpace))

import qualified Rank2
import Text.Grampa.Class (GrammarParsing(..), MonoidParsing(..), MultiParsing(..), ParseResults)
import Text.Grampa.ContextFree.Memoizing (ResultList(..), fromResultList)
import qualified Text.Grampa.ContextFree.Memoizing as Memoizing
import qualified Text.Grampa.PEG.Backtrack.Length as Backtrack

import Prelude hiding (cycle, null, span, takeWhile)

type Parser = Fixed Memoizing.Parser

data Fixed p g s a =
   Parser {
      complete, direct, direct0, direct1, indirect :: p g s a,
      cyclicDescendants :: Rank2.Apply g => g (Const (ParserFlags g)) -> ParserFlags g}
   | DirectParser {
      complete, direct0, direct1 :: p g s a}
   | PositiveDirectParser {
      complete :: p g s a}

data SeparatedParser p g s a = FrontParser (p g s a)
                             | CycleParser {
                                  cycleParser  :: p g s a,
                                  backParser   :: p g s a,
                                  dependencies :: g (Const Bool)}
                             | BackParser {
                                  backParser :: p g s a}

data ParserFlags g = ParserFlags {
   nullable :: Bool,
   dependsOn :: g (Const Bool)}

deriving instance Show (g (Const Bool)) => Show (ParserFlags g)

data ParserFunctor g s a = ParserResultsFunctor {parserResults :: ResultList g s a}
                         | ParserFlagsFuntor {parserFlags :: ParserFlags g}
                         | ParserFlagFunctor {parserFlag :: Bool}

newtype Union (g :: (* -> *) -> *) = Union{getUnion :: g (Const Bool)}

--instance Rank2.Applicative g => Monoid (Union g) where
--   mempty = Union (Rank2.pure $ Const False)

instance (Rank2.Apply g, Rank2.Distributive g) => Monoid (Union g) where
   mempty = Union (Rank2.distributeWith (Const . getConst) (Const False))
   mappend (Union g1) (Union g2) = Union (Rank2.liftA2 union g1 g2)

general, general' :: Alternative (p g s) => Fixed p g s a -> Fixed p g s a

general p = Parser{
   complete= complete p,
   direct = direct p',
   direct0= direct0 p',
   direct1= direct1 p',
   indirect= indirect p',
   cyclicDescendants= cyclicDescendants p'}
   where p' = general' p

general' p@PositiveDirectParser{} = Parser{
   complete= complete p,
   direct = complete p,
   direct0= empty,
   direct1= complete p,
   indirect= empty,
   cyclicDescendants= \cd-> ParserFlags False (const (Const False) Rank2.<$> cd)}
general' p@DirectParser{} = Parser{
   complete= complete p,
   direct = complete p,
   direct0= direct0 p,
   direct1= direct1 p,
   indirect= empty,
   cyclicDescendants= \cd-> ParserFlags True (const (Const False) Rank2.<$> cd)}
general' p@Parser{} = p

-- | Parser of general context-free grammars, including left recursion.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Apply' g, "Rank2".'Rank2.Traversable' g, 'FactorialMonoid' s) =>
--                  g (LeftRecursive.'Fixed g s) -> s -> g ('Compose' 'ParseResults' [])
-- @
instance MultiParsing (Fixed Memoizing.Parser) where
   type GrammarConstraint (Fixed Memoizing.Parser) g = (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g)
   type ResultFunctor (Fixed Memoizing.Parser) = Compose ParseResults []
   parsePrefix :: (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g, FactorialMonoid s) =>
                  g (Fixed Memoizing.Parser g s) -> s -> g (Compose (Compose ParseResults []) ((,) s))
   parsePrefix g input = Rank2.fmap (Compose . Compose . fromResultList input)
                                    (snd $ head $ parseRecursive g input)
   parseComplete :: (FactorialMonoid s, Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g) =>
                    g (Fixed Memoizing.Parser g s) -> s -> g (Compose ParseResults [])
   parseComplete g input = Rank2.fmap ((snd <$>) . Compose . fromResultList input)
                                      (snd $ head $ Memoizing.reparseTails close $ parseRecursive g input)
      where close = Rank2.fmap (<* endOfInput) selfReferring

instance GrammarParsing (Fixed Memoizing.Parser) where
   type GrammarFunctor (Fixed Memoizing.Parser) = ParserFunctor
   nonTerminal :: forall g s a. (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g)
                  => (g (ParserFunctor g s) -> ParserFunctor g s a) -> Parser g s a
   nonTerminal f = Parser{
      complete= ind,
      direct= empty,
      direct0= empty,
      direct1= empty,
      indirect= ind,
      cyclicDescendants= parserFlags . f . Rank2.fmap (ParserFlagsFuntor . getConst) . addSelf}
      where ind = nonTerminal (parserResults . f . Rank2.fmap ParserResultsFunctor)
            addSelf g = Rank2.liftA2 adjust bits g
            adjust :: forall b. Const (g (Const Bool)) b -> Const (ParserFlags g) b -> Const (ParserFlags g) b
            adjust (Const bit) (Const (ParserFlags n d)) =
               Const ParserFlags{
                  nullable= n, 
                  dependsOn= Rank2.liftA2 union bit d}
   recursive = general

bits :: forall (g :: (* -> *) -> *). (Rank2.Distributive g, Rank2.Traversable g) => g (Const (g (Const Bool)))
bits = start `seq` Rank2.fmap oneBit start
   where start = evalState (Rank2.traverse next (Rank2.distributeJoin Nothing)) 0
         oneBit :: Const Int a -> Const (g (Const Bool)) a
         next :: f a -> State Int (Const Int a)
         oneBit (Const i) = Const (Rank2.fmap (Const . (i ==) . getConst) start)
         next _ = do {i <- get; let {i' = succ i}; seq i' (put i'); return (Const i)}

instance Functor (p g s) => Functor (Fixed p g s) where
   fmap f (PositiveDirectParser p) = PositiveDirectParser (fmap f p)
   fmap f p@DirectParser{} = DirectParser{
      complete= fmap f (complete p),
      direct0= fmap f (direct0 p),
      direct1= fmap f (direct1 p)}
   fmap f p@Parser{} = p{
      complete= fmap f (complete p),
      direct= fmap f (direct p),
      direct0= fmap f (direct0 p),
      direct1= fmap f (direct1 p),
      indirect= fmap f (indirect p)}

instance Alternative (p g s) => Applicative (Fixed p g s) where
   pure a = DirectParser{complete= pure a,
                         direct0= pure a,
                         direct1= empty}
   p@PositiveDirectParser{} <*> q = PositiveDirectParser{
      complete= complete p <*> complete q}
   p@DirectParser{} <*> q@PositiveDirectParser{} = PositiveDirectParser{
      complete= complete p <*> complete q}
   p@DirectParser{} <*> q@DirectParser{} = DirectParser{
      complete= complete p <*> complete q,
      direct0= direct0 p <*> direct0 q,
      direct1= direct0 p <*> direct1 q <|> direct1 p <*> complete q}
   p <*> q@Parser{} = Parser{
      complete= complete p' <*> complete q,
      direct= direct0 p' <*> direct q <|> direct1 p' <*> complete q,
      direct0= direct0 p' <*> direct0 q,
      direct1= direct0 p' <*> direct1 q <|> direct1 p' <*> complete q,
      indirect= direct0 p' <*> indirect q <|> indirect p' <*> complete q,
      cyclicDescendants= \deps-> let
           pcd@(ParserFlags pn pd) = cyclicDescendants p' deps
           ParserFlags qn qd = cyclicDescendants q deps
        in if pn
           then ParserFlags qn (Rank2.liftA2 union pd qd)
           else pcd}
      where p'@Parser{} = general' p
   p <*> q = Parser{
      complete= complete p' <*> complete q',
      direct= direct p' <*> complete q',
      direct0= direct0 p' <*> direct0 q',
      direct1= direct0 p' <*> direct1 q' <|> direct1 p' <*> complete q',
      indirect= indirect p' <*> complete q',
      cyclicDescendants= \deps-> let
           pcd@(ParserFlags pn pd) = cyclicDescendants p' deps
           ParserFlags qn qd = cyclicDescendants q' deps
        in if pn
           then ParserFlags qn (Rank2.liftA2 union pd qd)
           else pcd}
      where p'@Parser{} = general' p
            q'@Parser{} = general' q

instance Alternative (p g s) => Alternative (Fixed p g s) where
   empty = PositiveDirectParser{complete= empty}
   p@PositiveDirectParser{} <|> q@PositiveDirectParser{} = PositiveDirectParser{complete= complete p <|> complete q}
   p@PositiveDirectParser{} <|> q@DirectParser{} = DirectParser{
      complete= complete p <|> complete q,
      direct0 = direct0 q,
      direct1= complete p <|> direct1 q}
   p@DirectParser{} <|> q@PositiveDirectParser{} = DirectParser{
      complete= complete p <|> complete q,
      direct0 = direct0 p,
      direct1= direct1 p <|> complete q}
   p@DirectParser{} <|> q@DirectParser{} = DirectParser{
      complete= complete p <|> complete q,
      direct0 = direct0 p <|> direct0 q,
      direct1= direct1 p <|> direct1 q}
   p <|> q = Parser{complete= complete p' <|> complete q',
                    direct= direct p' <|> direct q',
                    direct0= direct0 p' <|> direct0 q',
                    direct1= direct1 p' <|> direct1 q',
                    indirect= indirect p' <|> indirect q',
                    cyclicDescendants= \deps-> let
                         ParserFlags pn pd = cyclicDescendants p' deps
                         ParserFlags qn qd = cyclicDescendants q' deps
                      in ParserFlags (pn || qn) (Rank2.liftA2 union pd qd)}
      where p'@Parser{} = general p
            q'@Parser{} = general q
   many (PositiveDirectParser p) = DirectParser{
      complete= many p,
      direct0= pure [],
      direct1= some p}
   many p@DirectParser{} = DirectParser{
      complete= many (complete p),
      direct0= pure [] <|> (:[]) <$> direct0 p,
      direct1= (:) <$> direct1 p <*> many (complete p)}
   many p@Parser{} = Parser{
      complete= mcp,
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= (:) <$> indirect p <*> mcp,
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}
      where d0 = pure [] <|> (:[]) <$> direct0 p
            d1 = (:) <$> direct1 p <*> mcp
            mcp = many (complete p)
   some (PositiveDirectParser p) = PositiveDirectParser{complete= some p}
   some p@DirectParser{} = DirectParser{
      complete= some (complete p),
      direct0= (:[]) <$> direct0 p,
      direct1= (:) <$> direct1 p <*> many (complete p)}
   some p@Parser{} = Parser{
      complete= some (complete p),
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= (:) <$> indirect p <*> many (complete p),
      cyclicDescendants= cyclicDescendants p}
      where d0 = (:[]) <$> direct0 p
            d1= (:) <$> direct1 p <*> many (complete p)

union :: Const Bool x -> Const Bool x -> Const Bool x
union (Const False) d = d
union (Const True) _ = Const True

instance (Alternative (p g s), Monad (p g s)) => Monad (Fixed p g s) where
   return = pure
   (>>) = (*>)
   PositiveDirectParser p >>= cont = PositiveDirectParser (p >>= complete . cont)
   p@DirectParser{} >>= cont = Parser{
      complete= complete p >>= complete . cont,
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= direct0 p >>= indirect . general' . cont,
      cyclicDescendants= \cd-> (ParserFlags True $ Rank2.fmap (const $ Const True) cd)}
      where d0 = direct0 p >>= direct0 . general' . cont
            d1 = (direct0 p >>= direct1 . general' . cont) <|> (direct1 p >>= complete . cont)
   p >>= cont = Parser{
      complete= complete p >>= complete . cont,
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= (indirect p >>= complete . cont) <|> (direct0 p >>= indirect . general' . cont),
      cyclicDescendants= \cd-> (ParserFlags True $ Rank2.fmap (const $ Const True) cd)}
      where d0 = direct0 p >>= direct0 . general' . cont
            d1 = (direct0 p >>= direct1 . general' . cont) <|> (direct1 p >>= complete . cont)

instance MonadPlus (p g s) => MonadPlus (Fixed p g s) where
   mzero = empty
   mplus = (<|>)

instance (Alternative (p g s), Monoid x) => Monoid (Fixed p g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

primitive :: String -> p g s a -> p g s a -> p g s a -> Fixed p g s a
primitive _name d0 d1 d = DirectParser{complete= d,
                                       direct0= d0,
                                       direct1= d1}

positivePrimitive :: String -> p g s a -> Fixed p g s a
positivePrimitive _name p = PositiveDirectParser{complete= p}

instance (LookAheadParsing (p g s), MonoidParsing (Fixed p g)) => Parsing (Fixed p g s) where
   eof = primitive "eof" eof empty eof
   try (PositiveDirectParser p) = PositiveDirectParser (try p)
   try p@DirectParser{} = DirectParser{
      complete= try (complete p),
      direct0= try (direct0 p),
      direct1= try (direct1 p)}
   try p@Parser{} = p{
      complete= try (complete p),
      direct= try (direct p),
      direct0= try (direct0 p),
      direct1= try (direct1 p),
      indirect= try (indirect p)}
   PositiveDirectParser p <?> msg = PositiveDirectParser (p <?> msg)
   p@DirectParser{} <?> msg = DirectParser{
      complete= complete p <?> msg,
      direct0= direct0 p <?> msg,
      direct1= direct1 p <?> msg}
   p@Parser{} <?> msg = p{
      complete= complete p <?> msg,
      direct= direct p <?> msg,
      direct0= direct0 p <?> msg,
      direct1= direct1 p <?> msg,
      indirect= indirect p <?> msg}
   notFollowedBy p@PositiveDirectParser{} = DirectParser{
      complete= notFollowedBy (complete p),
      direct0= notFollowedBy (complete p),
      direct1= empty}
   notFollowedBy p@DirectParser{} = DirectParser{
      complete= notFollowedBy (complete p),
      direct0= notFollowedBy (complete p),
      direct1= empty}
   notFollowedBy p@Parser{} = Parser{
      complete= notFollowedBy (complete p),
      direct= notFollowedBy (direct p),
      direct0= notFollowedBy (direct p),
      direct1= empty,
      indirect= notFollowedBy (indirect p),
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}
   unexpected msg = positivePrimitive "unexpected" (unexpected msg)
   skipMany p = concatMany (() <$ p)

instance (LookAheadParsing (p g s), MonoidParsing (Fixed p g)) => LookAheadParsing (Fixed p g s) where
   lookAhead p@PositiveDirectParser{} = DirectParser{
      complete= lookAhead (complete p),
      direct0= lookAhead (complete p),
      direct1= empty}
   lookAhead p@DirectParser{} = DirectParser{
      complete= lookAhead (complete p),
      direct0= lookAhead (complete p),
      direct1= empty}
   lookAhead p@Parser{} = Parser{
      complete= lookAhead (complete p),
      direct= lookAhead (direct p),
      direct0= lookAhead (direct p),
      direct1= empty,
      indirect= lookAhead (indirect p),
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}

instance MonoidParsing (Fixed Memoizing.Parser g) where
   endOfInput = primitive "endOfInput" endOfInput empty endOfInput
   getInput = primitive "getInput" (endOfInput *> getInput) (notFollowedBy endOfInput *> getInput) getInput
   anyToken = positivePrimitive "anyToken" anyToken
   token x = positivePrimitive "token" (token x)
   satisfy predicate = positivePrimitive "satisfy" (satisfy predicate)
   satisfyChar predicate = positivePrimitive "satisfyChar" (satisfyChar predicate)
   satisfyCharInput predicate = positivePrimitive "satisfyCharInput" (satisfyCharInput predicate)
   notSatisfy predicate = primitive "notSatisfy" (notSatisfy predicate) empty (notSatisfy predicate)
   notSatisfyChar predicate = primitive "notSatisfyChar" (notSatisfyChar predicate) empty (notSatisfyChar predicate)
   scan s0 f = primitive "scan" (mempty <$ notSatisfy test) (lookAhead (satisfy test) *> p) p
      where p = scan s0 f
            test = isJust . f s0
   scanChars s0 f = primitive "scanChars" (mempty <$ notSatisfyChar test) (lookAhead (satisfyChar test) *> p) p
      where p = scanChars s0 f
            test = isJust . f s0
   string s
      | null s = primitive ("(string " ++ shows s ")") (string s) empty (string s)
      | otherwise = positivePrimitive ("(string " ++ shows s ")") (string s)
   takeWhile predicate = primitive "takeWhile" (mempty <$ notSatisfy predicate)
                                               (takeWhile1 predicate) (takeWhile predicate)
   takeWhile1 predicate = positivePrimitive "takeWhile1" (takeWhile1 predicate)
   takeCharsWhile predicate = primitive "takeCharsWhile" (mempty <$ notSatisfyChar predicate)
                                                         (takeCharsWhile1 predicate) (takeCharsWhile predicate)
   takeCharsWhile1 predicate = positivePrimitive "takeCharsWhile1" (takeCharsWhile1 predicate)
   whiteSpace = primitive "whiteSpace" (notSatisfyChar isSpace) (satisfyChar isSpace *> whiteSpace) whiteSpace
   concatMany p@PositiveDirectParser{} = DirectParser{
      complete= cmp,
      direct0= d0,
      direct1= d1}
      where d0 = pure mempty
            d1 = (<>) <$> complete p <*> cmp
            cmp = concatMany (complete p)
   concatMany p@DirectParser{} = DirectParser{
      complete= cmp,
      direct0= d0,
      direct1= d1}
      where d0 = pure mempty <|> direct0 p
            d1 = (<>) <$> direct1 p <*> cmp
            cmp = concatMany (complete p)
   concatMany p@Parser{} = Parser{
      complete= cmp,
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= (<>) <$> indirect p <*> cmp,
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}
      where d0 = pure mempty <|> direct0 p
            d1 = (<>) <$> direct1 p <*> cmp
            cmp = concatMany (complete p)

instance MonoidParsing (Fixed Backtrack.Parser g) where
   endOfInput = primitive "endOfInput" endOfInput empty endOfInput
   getInput = primitive "getInput" (endOfInput *> getInput) (notFollowedBy endOfInput *> getInput) getInput
   anyToken = positivePrimitive "anyToken" anyToken
   token x = positivePrimitive "token" (token x)
   satisfy predicate = positivePrimitive "satisfy" (satisfy predicate)
   satisfyChar predicate = positivePrimitive "satisfyChar" (satisfyChar predicate)
   satisfyCharInput predicate = positivePrimitive "satisfyCharInput" (satisfyCharInput predicate)
   notSatisfy predicate = primitive "notSatisfy" (notSatisfy predicate) empty (notSatisfy predicate)
   notSatisfyChar predicate = primitive "notSatisfyChar" (notSatisfyChar predicate) empty (notSatisfyChar predicate)
   scan s0 f = primitive "scan" (mempty <$ notSatisfy test) (lookAhead (satisfy test) *> p) p
      where p = scan s0 f
            test = isJust . f s0
   scanChars s0 f = primitive "scanChars" (mempty <$ notSatisfyChar test) (lookAhead (satisfyChar test) *> p) p
      where p = scanChars s0 f
            test = isJust . f s0
   string s
      | null s = primitive ("(string " ++ shows s ")") (string s) empty (string s)
      | otherwise = positivePrimitive ("(string " ++ shows s ")") (string s)
   takeWhile predicate = primitive "takeWhile" (mempty <$ notSatisfy predicate)
                                               (takeWhile1 predicate) (takeWhile predicate)
   takeWhile1 predicate = positivePrimitive "takeWhile1" (takeWhile1 predicate)
   takeCharsWhile predicate = primitive "takeCharsWhile" (mempty <$ notSatisfyChar predicate)
                                                         (takeCharsWhile1 predicate) (takeCharsWhile predicate)
   takeCharsWhile1 predicate = positivePrimitive "takeCharsWhile1" (takeCharsWhile1 predicate)
   whiteSpace = primitive "whiteSpace" (notSatisfyChar isSpace) (satisfyChar isSpace *> whiteSpace) whiteSpace
   concatMany p@PositiveDirectParser{} = DirectParser{
      complete= cmp,
      direct0= d0,
      direct1= d1}
      where d0 = pure mempty
            d1 = (<>) <$> complete p <*> cmp
            cmp = concatMany (complete p)
   concatMany p@DirectParser{} = DirectParser{
      complete= cmp,
      direct0= d0,
      direct1= d1}
      where d0 = pure mempty `Backtrack.alt` direct0 p
            d1 = (<>) <$> direct1 p <*> cmp
            cmp = concatMany (complete p)
   concatMany p@Parser{} = Parser{
      complete= cmp,
      direct= d0 `Backtrack.alt` d1,
      direct0= d0,
      direct1= d1,
      indirect= (<>) <$> indirect p <*> cmp,
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}
      where d0 = pure mempty `Backtrack.alt` direct0 p
            d1 = (<>) <$> direct1 p <*> cmp
            cmp = concatMany (complete p)

instance (LookAheadParsing (p g s), MonoidParsing (Fixed p g), Show s, TextualMonoid s) =>
         CharParsing (Fixed p g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (LookAheadParsing (p g s), TokenParsing (p g s), MonoidParsing (Fixed p g), Show s, TextualMonoid s) => 
         TokenParsing (Fixed p g s) where
   someSpace = positivePrimitive "someSpace" someSpace

-- | Turns a context-free parser into a backtracking PEG parser that consumes the longest possible prefix of the list
-- of input tails, opposite of 'peg'
longest :: FactorialMonoid s => Fixed Memoizing.Parser g s a -> Fixed Backtrack.Parser g [(s, g (ResultList g s))] a
longest (PositiveDirectParser p) = PositiveDirectParser (Memoizing.longest p)
longest p@DirectParser{} = DirectParser{complete= Memoizing.longest (complete p),
                                        direct0=  Memoizing.longest (direct0 p),
                                        direct1=  Memoizing.longest (direct1 p)}
longest p@Parser{} = Parser{complete= Memoizing.longest (complete p),
                            direct=  Memoizing.longest (direct p),
                            direct0=  Memoizing.longest (direct0 p),
                            direct1=  Memoizing.longest (direct1 p),
                            indirect=  Memoizing.longest (indirect p),
                            cyclicDescendants= cyclicDescendants p}

-- | Turns a backtracking PEG parser of the list of input tails into a context-free parser, opposite of 'longest'
peg :: Fixed Backtrack.Parser g [(s, g (ResultList g s))] a -> Fixed Memoizing.Parser g s a
peg (PositiveDirectParser p) = PositiveDirectParser (Memoizing.peg p)
peg p@DirectParser{} = DirectParser{complete= Memoizing.peg (complete p),
                                        direct0=  Memoizing.peg (direct0 p),
                                        direct1=  Memoizing.peg (direct1 p)}
peg p@Parser{} = Parser{complete= Memoizing.peg (complete p),
                        direct=  Memoizing.peg (direct p),
                        direct0=  Memoizing.peg (direct0 p),
                        direct1=  Memoizing.peg (direct1 p),
                        indirect=  Memoizing.peg (indirect p),
                        cyclicDescendants= cyclicDescendants p}

-- | Turns a backtracking PEG parser into a context-free parser
terminalPEG :: Monoid s => Fixed Backtrack.Parser g s a -> Fixed Memoizing.Parser g s a
terminalPEG (PositiveDirectParser p) = PositiveDirectParser (Memoizing.terminalPEG p)
terminalPEG p@DirectParser{} = DirectParser{complete= Memoizing.terminalPEG (complete p),
                                            direct0=  Memoizing.terminalPEG (direct0 p),
                                            direct1=  Memoizing.terminalPEG (direct1 p)}
terminalPEG p@Parser{} = Parser{complete= Memoizing.terminalPEG (complete p),
                                direct=  Memoizing.terminalPEG (direct p),
                                direct0=  Memoizing.terminalPEG (direct0 p),
                                direct1=  Memoizing.terminalPEG (direct1 p),
                                indirect=  Memoizing.terminalPEG (indirect p),
                                cyclicDescendants= cyclicDescendants p}

parseRecursive :: forall g s. (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g, FactorialMonoid s) =>
                  g (Fixed Memoizing.Parser g s) -> s -> [(s, g (ResultList g s))]
parseRecursive = parseSeparated . separated

separated :: forall g s. (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g) =>
             g (Fixed Memoizing.Parser g s) -> g (SeparatedParser Memoizing.Parser g s)
separated g = Rank2.liftA4 reseparate circulars cycleFollowers descendants g
   where descendants :: g (Const (g (Const Bool)))
         cycleFollowers, circulars :: g (Const Bool)
         cyclicDescendantses :: g (Const (ParserFlags g))
         leftRecursive :: forall a. Const (g (Const Bool)) a -> Const (ParserFlags g) a -> Const Bool a
         leftRecursiveDeps :: forall a. Const Bool a -> Const (ParserFlags g) a -> Const (g (Const Bool)) a
         reseparate :: forall a. Const Bool a -> Const Bool a -> Const (g (Const Bool)) a -> Parser g s a
                    -> SeparatedParser Memoizing.Parser g s a
         reseparate (Const circular) (Const follower) (Const deps) p
            | circular || leader && follower = CycleParser (indirect p) (direct p) deps
            | follower = BackParser (complete p)
            | otherwise = FrontParser (complete p)
            where leader = getAny (Rank2.foldMap (Any . getConst) $ Rank2.liftA2 intersection circulars deps)
         descendants = Rank2.fmap (Const . dependsOn . getConst) cyclicDescendantses
         cyclicDescendantses = fixDescendants (Rank2.fmap (Const . cyclicDescendants . general) g)
         circulars = Rank2.liftA2 leftRecursive bits cyclicDescendantses
         cycleFollowers = getUnion (Rank2.foldMap (Union . getConst) $
                                    Rank2.liftA2 leftRecursiveDeps circulars cyclicDescendantses)
         leftRecursive (Const bit) (Const flags) =
            Const (getAny $ Rank2.foldMap (Any . getConst) $ Rank2.liftA2 intersection bit $ dependsOn flags)
         leftRecursiveDeps (Const True) (Const flags) = Const (dependsOn flags)
         leftRecursiveDeps (Const False) (Const flags) = Const (Rank2.fmap (const $ Const False) (dependsOn flags))
         intersection (Const a) (Const b) = Const (a && b)

fixDescendants :: forall g. (Rank2.Apply g, Rank2.Traversable g)
                     => g (Const (g (Const (ParserFlags g)) -> (ParserFlags g))) -> g (Const (ParserFlags g))
fixDescendants gf = go initial
   where go :: g (Const (ParserFlags g)) -> g (Const (ParserFlags g))
         go cd
            | getAll (Rank2.foldMap (All . getConst) $ Rank2.liftA2 agree cd cd') = cd
            | otherwise = go cd'
            where cd' = Rank2.liftA2 depsUnion cd (Rank2.fmap (\(Const f)-> Const (f cd)) gf)
         agree (Const (ParserFlags xn xd)) (Const (ParserFlags yn yd)) =
            Const (getAll (Rank2.foldMap (All . getConst) (Rank2.liftA2 agree' xd yd)))
         agree' (Const x) (Const y) = Const (x == y)
         depsUnion (Const ParserFlags{dependsOn= old}) (Const (ParserFlags n new)) = 
            Const (ParserFlags n $ Rank2.liftA2 union old new)
         initial = Rank2.liftA2 (\_ (Const n)-> Const (ParserFlags n (const (Const False) Rank2.<$> gf))) gf nullabilities
         nullabilities = fixNullabilities gf

fixNullabilities :: forall g. (Rank2.Apply g, Rank2.Traversable g)
                    => g (Const (g (Const (ParserFlags g)) -> (ParserFlags g))) -> g (Const Bool)
fixNullabilities gf = Rank2.fmap (Const . nullable . getConst) (go initial)
   where go :: g (Const (ParserFlags g)) -> g (Const (ParserFlags g))
         go cd
            | getAll (Rank2.foldMap (All . getConst) $ Rank2.liftA2 agree cd cd') = cd
            | otherwise = go cd'
            where cd' = Rank2.fmap (\(Const f)-> Const (f cd)) gf
         agree (Const flags1) (Const flags2) = Const (nullable flags1 == nullable flags2)
         initial = const (Const (ParserFlags True (const (Const False) Rank2.<$> gf))) Rank2.<$> gf

-- | Parse the given input using a context-free grammar separated into two parts: the first specifying all the
-- left-recursive productions, the second all others. The first function argument specifies the left-recursive
-- dependencies among the grammar productions.
parseSeparated :: forall g s. (Rank2.Apply g, Rank2.Foldable g, FactorialMonoid s) =>
                  g (SeparatedParser Memoizing.Parser g s) -> s -> [(s, g (ResultList g s))]
parseSeparated parsers input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d''):parsedTail
                  d      = Rank2.fmap (($ (s,d):parsedTail) . Memoizing.applyParser) directs
                  d'     = fixRecursive s parsedTail d
                  d''    = Rank2.liftA2 f parsers d'
                  f :: forall a. SeparatedParser Memoizing.Parser g s a -> ResultList g s a -> ResultList g s a
                  f (FrontParser p) _ = Memoizing.applyParser p ((s,d''):parsedTail)
                  f _ result = result
         fixRecursive :: s -> [(s, g (ResultList g s))] -> g (ResultList g s) -> g (ResultList g s)
         whileAnyContinues :: g (ResultList g s) -> g (ResultList g s) -> g (ResultList g s)
         recurseOnce :: s -> [(s, g (ResultList g s))] -> g (ResultList g s) -> g (ResultList g s)
         maybeDependencies :: g (Const (Maybe (g (Const Bool))))

         directs = Rank2.fmap backParser parsers
         indirects = Rank2.fmap (\p-> case p of {CycleParser{}-> cycleParser p; _ -> empty}) parsers
         maybeDependencies = Rank2.fmap (Const . maybeDependency) parsers
         maybeDependency p@CycleParser{} = Just (dependencies p)
         maybeDependency _ = Nothing
                                                                   
         fixRecursive s parsedTail initial =
            foldr1 whileAnyContinues (iterate (recurseOnce s parsedTail) initial)

         whileAnyContinues g1 g2 = Rank2.liftA3 choiceWhile maybeDependencies g1 g2
            where choiceWhile :: Const (Maybe (g (Const Bool))) x -> ResultList g i x -> ResultList g i x 
                                 -> ResultList g i x
                  combine :: Const Bool x -> ResultList g i x -> Const Bool x
                  choiceWhile (Const Nothing) r1 _ = r1
                  choiceWhile (Const (Just deps)) r1 r2
                     | getAny (Rank2.foldMap (Any . getConst) (Rank2.liftA2 combine deps g1)) = r1 <> r2
                     | otherwise = r1
                  combine (Const False) _ = Const False
                  combine (Const True) (ResultList [] _) = Const False
                  combine (Const True) _ = Const True

         recurseOnce s parsedTail initial = Rank2.fmap (($ parsed) . Memoizing.applyParser) indirects
            where parsed = (s, initial):parsedTail
