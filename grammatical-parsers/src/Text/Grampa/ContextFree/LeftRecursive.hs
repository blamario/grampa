{-# LANGUAGE FlexibleContexts, GADTs, InstanceSigs, GeneralizedNewtypeDeriving,
             RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeFamilies #-}
{-# OPTIONS -fno-full-laziness #-}
module Text.Grampa.ContextFree.LeftRecursive (Parser, parseSeparated)
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
import Text.Grampa.ContextFree.Memoizing (ResultList(..), fromResultList, notSatisfy, notSatisfyChar)
import qualified Text.Grampa.ContextFree.Memoizing as Memoizing

import Prelude hiding (null, showsPrec, span, takeWhile)

data Parser g s a =
   Parser {
      complete, direct, direct0, direct1, indirect :: Memoizing.Parser g s a,
      cyclicDescendants :: Rank2.Apply g => g (Const (Bool, Bool, g (Const Bool))) -> (Bool, Bool, g (Const Bool))}
   | DirectParser {
      complete, direct0, direct1 :: Memoizing.Parser g s a}
   | PositiveDirectParser {
      complete :: Memoizing.Parser g s a}

data ParserFunctor g s a = ParserFunctor {
   resultListF :: ResultList g s a,
   cyclicDescendantsF :: (Bool, Bool, g (Const Bool))}

general, general' :: Parser g s a -> Parser g s a

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
   cyclicDescendants= \cd-> (False, False, const (Const False) Rank2.<$> cd)}
general' p@DirectParser{} = Parser{
   complete= complete p,
   direct = complete p,
   direct0= direct0 p,
   direct1= direct1 p,
   indirect= empty,
   cyclicDescendants= \cd-> (True, False, const (Const False) Rank2.<$> cd)}
general' p@Parser{} = p

-- | Parser of general context-free grammars, including left recursion.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Apply' g, "Rank2".'Rank2.Traversable' g, 'FactorialMonoid' s) =>
--                  g (LeftRecursive.'Parser' g s) -> s -> g ('Compose' 'ParseResults' [])
-- @
instance MultiParsing Parser where
   type GrammarConstraint Parser g = (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g)
   type ResultFunctor Parser = Compose ParseResults []
   parsePrefix :: (Rank2.Apply g, Rank2.Traversable g, FactorialMonoid s) =>
                  g (Parser g s) -> s -> g (Compose (Compose ParseResults []) ((,) s))
   parsePrefix g input = Rank2.fmap (Compose . Compose . fromResultList input)
                                    (snd $ head $ parseRecursive g input)
   parseComplete :: (FactorialMonoid s, Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g) =>
                    g (Parser g s) -> s -> g (Compose ParseResults [])
   parseComplete g input = Rank2.fmap ((snd <$>) . Compose . fromResultList input)
                                      (snd $ head $ Memoizing.reparseTails close $ parseRecursive g input)
      where close = Rank2.fmap (<* endOfInput) selfReferring

instance GrammarParsing Parser where
   type GrammarFunctor Parser = ParserFunctor
   nonTerminal :: forall g s a. (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g)
                  => (g (ParserFunctor g s) -> ParserFunctor g s a) -> Parser g s a
   nonTerminal f = Parser{
      complete= ind,
      direct= empty,
      direct0= empty,
      direct1= empty,
      indirect= ind,
      cyclicDescendants= cyclicDescendantsF . f . addSelf . Rank2.fmap wrapCyclicDescendants}
      where ind = nonTerminal (resultListF . f . Rank2.fmap wrapResultList)
            wrapCyclicDescendants (Const cd) = ParserFunctor{cyclicDescendantsF= cd,
                                                             resultListF= error "resultListF of wrapCyclicDescendants"}
            wrapResultList rl = ParserFunctor{resultListF= rl,
                                              cyclicDescendantsF= error "cyclicDescendantsF of wrapResultList"}
            addSelf g = Rank2.liftA2 adjust bits g
            adjust :: forall b. Const (g (Const Bool)) b -> ParserFunctor g s b -> ParserFunctor g s b
            adjust (Const bit) pf@ParserFunctor{cyclicDescendantsF= (n, c, d)} =
               pf{cyclicDescendantsF= (n,
                                       c || getAny (Rank2.foldMap (Any . getConst) $ Rank2.liftA2 (onConst (&&)) bit d),
                                       Rank2.liftA2 (onConst (||)) bit d)}
            onConst f1 (Const a) (Const b) = Const (f1 a b)
   recursive = general

bits :: forall (g :: (* -> *) -> *). (Rank2.Distributive g, Rank2.Traversable g) => g (Const (g (Const Bool)))
bits = start `seq` Rank2.fmap oneBit start
   where start = evalState (Rank2.traverse next (Rank2.distributeM Nothing)) 0
         oneBit :: Const Int a -> Const (g (Const Bool)) a
         next :: f a -> State Int (Const Int a)
         oneBit (Const i) = Const (Rank2.fmap (Const . (i ==) . getConst) start)
         next _ = do {i <- get; let {i' = succ i}; seq i' (put i'); return (Const i)}

instance Functor (Parser g s) where
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

instance Applicative (Parser g s) where
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
           pcd@(pn, pc, pd) = cyclicDescendants p' deps
           (qn, qc, qd) = cyclicDescendants q deps
        in if pn
           then (qn, pc || qc, Rank2.liftA2 union pd qd)
           else pcd}
      where p'@Parser{} = general' p
   p <*> q = Parser{
      complete= complete p' <*> complete q',
      direct= direct p' <*> complete q',
      direct0= direct0 p' <*> direct0 q',
      direct1= direct0 p' <*> direct1 q' <|> direct1 p' <*> complete q',
      indirect= indirect p' <*> complete q',
      cyclicDescendants= \deps-> let
           pcd@(pn, pc, pd) = cyclicDescendants p' deps
           (qn, qc, qd) = cyclicDescendants q' deps
        in if pn
           then (qn, pc || qc, Rank2.liftA2 union pd qd)
           else pcd}
      where p'@Parser{} = general' p
            q'@Parser{} = general' q

instance Alternative (Parser g s) where
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
                         (pn, pc, pd) = cyclicDescendants p' deps
                         (qn, qc, qd) = cyclicDescendants q' deps
                      in (pn || qn,
                          pc || qc,
                          Rank2.liftA2 union pd qd)}
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
      cyclicDescendants= \deps-> let
         (_, pc, pd) = cyclicDescendants p deps
         in (True, pc, pd)}
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
      cyclicDescendants= \deps-> let
           (pn, pc, pd) = cyclicDescendants p deps
        in (pn, pc, pd)}
      where d0 = (:[]) <$> direct0 p
            d1= (:) <$> direct1 p <*> many (complete p)

union :: Const Bool x -> Const Bool x -> Const Bool x
union (Const False) d = d
union (Const True) _ = Const True

instance Monad (Parser g s) where
   return = pure
   (>>) = (*>)
   PositiveDirectParser p >>= cont = PositiveDirectParser (p >>= complete . cont)
   p >>= cont = Parser{
      complete= complete p >>= complete . cont,
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= (indirect p >>= complete . cont) <|> (direct0 p >>= indirect . general' . cont),
      cyclicDescendants= cyclicDescendants p'}
      where d0 = direct0 p >>= direct0 . cont
            d1 = (direct0 p >>= direct1 . general' . cont) <|> (direct1 p >>= complete . cont)
            p' = general' p

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

primitive :: String -> Memoizing.Parser g s a -> Memoizing.Parser g s a -> Memoizing.Parser g s a
          -> Parser g s a
primitive _name d0 d1 d = DirectParser{complete= d,
                                       direct0= d0,
                                       direct1= d1}

positivePrimitive :: String -> Memoizing.Parser g s a -> Parser g s a
positivePrimitive _name p = PositiveDirectParser{complete= p}

instance MonoidNull s => Parsing (Parser g s) where
   eof = primitive "eof" eof empty eof
   try (PositiveDirectParser p) = PositiveDirectParser (try p)
   try p@DirectParser{} = DirectParser{
      complete= try (complete p),
      direct0= try (direct0 p),
      direct1= try (direct0 p)}
   try p@Parser{} = p{
      complete= try (complete p),
      direct= try (direct p),
      direct0= try (direct0 p),
      direct1= try (direct0 p),
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
      cyclicDescendants= \deps-> let (_, nc, nd) = cyclicDescendants p deps in (True, nc, nd)}
   unexpected msg = positivePrimitive "unexpected" (unexpected msg)
   skipMany = concatMany . (() <$)

instance MonoidNull s => LookAheadParsing (Parser g s) where
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
      cyclicDescendants= \deps-> let (_, nc, nd) = cyclicDescendants p deps in (True, nc, nd)}

instance MonoidParsing (Parser g) where
   endOfInput = primitive "endOfInput" endOfInput empty endOfInput
   getInput = primitive "getInput" (eof *> getInput) (notFollowedBy eof *> getInput) getInput
   anyToken = positivePrimitive "anyToken" anyToken
   token x = positivePrimitive "token" (token x)
   satisfy predicate = positivePrimitive "satisfy" (satisfy predicate)
   satisfyChar predicate = positivePrimitive "satisfyChar" (satisfyChar predicate)
   satisfyCharInput predicate = positivePrimitive "satisfyCharInput" (satisfyCharInput predicate)
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
      cyclicDescendants= \deps-> let
           (_, pc, pd) = cyclicDescendants p deps
        in (True, pc, pd)}
      where d0 = pure mempty <|> direct0 p
            d1 = (<>) <$> direct1 p <*> cmp
            cmp = concatMany (complete p)

instance (Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Show s, TextualMonoid s) => TokenParsing (Parser g s) where
   someSpace = () <$ takeCharsWhile1 isSpace

parseRecursive :: forall g s. (Rank2.Apply g, Rank2.Traversable g, FactorialMonoid s) =>
                  g (Parser g s) -> s -> [(s, g (ResultList g s))]
parseRecursive g = parseSeparated descendants indirects directs
   where descendants :: g (Const (g (Const Bool)))
         desc :: forall x. Const (Bool, Bool, g (Const Bool)) x -> Const (g (Const Bool)) x
         cyclicDescendantses :: g (Const (Bool, Bool, g (Const Bool)))
         descendants = Rank2.fmap desc cyclicDescendantses
         indirects = Rank2.liftA2 indirectOrEmpty cyclicDescendantses g
         directs = Rank2.liftA2 directOrComplete cyclicDescendantses g
         indirectOrEmpty (Const (_, cyclic, _)) p = if cyclic then indirect p else empty
         directOrComplete (Const (_, cyclic, _)) p = if cyclic then direct p else complete p
         desc (Const (_, cyclic, gd)) = Const (if cyclic then gd else falses)
         cyclicDescendantses = fixCyclicDescendants initial $ Rank2.fmap (Const . cyclicDescendants . general) g
         initial = const (Const (True, False, falses)) Rank2.<$> g
         falses = const (Const False) Rank2.<$> g

fixCyclicDescendants :: forall g. (Rank2.Apply g, Rank2.Traversable g)
                     => g (Const (Bool, Bool, g (Const Bool)))
                     -> g (Const (g (Const (Bool, Bool, g (Const Bool))) -> (Bool, Bool, g (Const Bool))))
                     -> g (Const (Bool, Bool, g (Const Bool)))
fixCyclicDescendants g gf = go g
   where go :: g (Const (Bool, Bool, g (Const Bool))) -> g (Const (Bool, Bool, g (Const Bool)))
         go cd
            | getAll (Rank2.foldMap (All . getConst) $ Rank2.liftA2 agree cd cd') = cd
            | otherwise = go cd'
            where cd' = Rank2.fmap (\(Const f)-> Const (f cd)) gf
         agree (Const (xn, xc, xd)) (Const (yn, yc, yd)) =
            Const (xn == yn && xc == yc && getAll (Rank2.foldMap (All . getConst) (Rank2.liftA2 agree' xd yd)))
         agree' (Const x) (Const y) = Const (x == y)

-- | Parse the given input using a context-free grammar separated into two parts: the first specifying all the
-- left-recursive productions, the second all others. The first function argument specifies the left-recursive
-- dependencies among the grammar productions.
parseSeparated :: forall g s. (Rank2.Apply g, Rank2.Foldable g, FactorialMonoid s) =>
                  g (Const (g (Const Bool))) -> g (Memoizing.Parser g s) -> g (Memoizing.Parser g s) -> s
               -> [(s, g (ResultList g s))]
parseSeparated dependencies indirects directs input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d'):parsedTail
                  d      = Rank2.fmap (($ (s,d):parsedTail) . Memoizing.applyParser) directs
                  d'     = fixRecursive s parsedTail d

         fixRecursive :: s -> [(s, g (ResultList g s))] -> g (ResultList g s) -> g (ResultList g s)
         whileAnyContinues :: g (ResultList g s) -> g (ResultList g s) -> g (ResultList g s)
         recurseOnce :: s -> [(s, g (ResultList g s))] -> g (ResultList g s) -> g (ResultList g s)

         fixRecursive s parsedTail initial =
            foldr1 whileAnyContinues (iterate (recurseOnce s parsedTail) initial)

         whileAnyContinues g1 g2 = Rank2.liftA3 choiceWhile dependencies g1 g2
            where choiceWhile :: Const (g (Const Bool)) x -> ResultList g i x -> ResultList g i x -> ResultList g i x
                  combine :: Const Bool x -> ResultList g i x -> Const Bool x
                  choiceWhile (Const deps) r1 r2
                     | getAny (Rank2.foldMap (Any . getConst) (Rank2.liftA2 combine deps g1)) = r1 <> r2
                     | otherwise = r1
                  combine (Const False) _ = Const False
                  combine (Const True) (ResultList [] _) = Const False
                  combine (Const True) _ = Const True

         recurseOnce s parsedTail initial = Rank2.fmap (($ parsed) . Memoizing.applyParser) indirects
            where parsed = (s, initial):parsedTail
