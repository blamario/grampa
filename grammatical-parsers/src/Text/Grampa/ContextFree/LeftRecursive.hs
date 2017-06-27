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
import Data.Maybe (fromMaybe, isJust)

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

data Parser g s a = Parser {
   complete, direct, direct0, direct1, indirect :: Memoizing.Parser g s a,
   cyclicDescendants :: Rank2.Apply g => g (Const (Bool, Bool, g (Const Bool))) -> (Bool, Bool, g (Const Bool))}

data ParserFunctor g s a = ParserFunctor {
   resultListF :: ResultList g s a,
   cyclicDescendantsF :: (Bool, Bool, g (Const Bool))}

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
            addSelf g = Rank2.liftA2 adjust (bits g) g
            adjust :: forall b. Const (g (Const Bool)) b -> ParserFunctor g s b -> ParserFunctor g s b
            adjust (Const bit) pf@ParserFunctor{cyclicDescendantsF= (n, c, d)} =
               pf{cyclicDescendantsF= (n,
                                       c || getAny (Rank2.foldMap (Any . getConst) $ Rank2.liftA2 (onConst (&&)) bit d),
                                       Rank2.liftA2 (onConst (||)) bit d)}
            onConst f1 (Const a) (Const b) = Const (f1 a b)
   recursive = id

bits :: Rank2.Traversable g => g f -> g (Const (g (Const Bool)))
bits g = evalState (Rank2.traverse next g) start 
   where start = shift True (const (Const False) Rank2.<$> g)
         next _ = do {prev <- get; put (shift False prev); return (Const prev)}

shift :: Rank2.Traversable g => Bool -> g (Const Bool) -> g (Const Bool)
shift newBit g = evalState (Rank2.traverse next g) newBit
   where next :: forall a. Const Bool a -> State Bool (Const Bool a)
         next (Const x) = do {prev <- get; put x; return (Const prev)}

instance Functor (Parser g s) where
   fmap f p = p{complete= fmap f (complete p),
                direct= fmap f (direct p),
                direct0= fmap f (direct0 p),
                direct1= fmap f (direct1 p),
                indirect= fmap f (indirect p)}

instance Applicative (Parser g s) where
   pure a = Parser{complete= pure a,
                   direct= pure a,
                   direct0= pure a,
                   direct1= empty,
                   indirect= empty,
                   cyclicDescendants= \g-> (True, False, const (Const False) Rank2.<$> g)}
   p <*> q = Parser{complete= complete p <*> complete q,
                    direct= direct0 p <*> direct q <|> direct1 p <*> complete q,
                    direct0= direct0 p <*> direct0 q,
                    direct1= direct0 p <*> direct1 q <|> direct1 p <*> complete q,
                    indirect= direct0 p <*> indirect q <|> indirect p <*> complete q,
                    cyclicDescendants= \deps-> let
                         pcd@(pn, pc, pd) = cyclicDescendants p deps
                         (qn, qc, qd) = cyclicDescendants q deps
                      in if pn
                         then (qn, pc || qc, Rank2.liftA2 union pd qd)
                         else pcd}

instance Alternative (Parser g s) where
   empty = Parser{complete= empty,
                  direct= empty,
                  direct0= empty,
                  direct1= empty,
                  indirect= empty,
                  cyclicDescendants= \g-> (False, False, const (Const False) Rank2.<$> g)}
   p <|> q = Parser{complete= complete p <|> complete q,
                    direct= direct p <|> direct q,
                    direct0= direct0 p <|> direct0 q,
                    direct1= direct1 p <|> direct1 q,
                    indirect= indirect p <|> indirect q,
                    cyclicDescendants= \deps-> let
                         (pn, pc, pd) = cyclicDescendants p deps
                         (qn, qc, qd) = cyclicDescendants q deps
                      in (pn || qn,
                          pc || qc,
                          Rank2.liftA2 union pd qd)}
   many p = Parser{complete= mcp,
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
   some p = Parser{complete= some (complete p),
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
   p >>= cont = Parser{complete= complete p >>= complete . cont,
                       direct= d0 <|> d1,
                       direct0= d0,
                       direct1= d1,
                       indirect= (indirect p >>= complete . cont) <|> (direct0 p >>= indirect . cont),
                       cyclicDescendants= cyclicDescendants p}
      where d0 = direct0 p >>= direct0 . cont
            d1 = (direct0 p >>= direct1 . cont) <|> (direct1 p >>= complete . cont)

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

primitive :: String -> Maybe (Memoizing.Parser g s a) -> Memoizing.Parser g s a -> Memoizing.Parser g s a
          -> Parser g s a
primitive _name d0 d1 d = Parser{complete= d,
                                 direct= d,
                                 direct0= fromMaybe empty d0,
                                 direct1= d1,
                                 indirect= empty,
                                 cyclicDescendants= \g-> (isJust d0, False, const (Const False) Rank2.<$> g)}

instance MonoidNull s => Parsing (Parser g s) where
   eof = primitive "eof" (Just eof) empty eof
   try p = p{complete= try (direct0 p),
             direct= try (direct p),
             direct0= try (direct0 p),
             direct1= try (direct0 p),
             indirect= try (indirect p)}
   p <?> msg = p{complete= complete p <?> msg,
                 direct= direct p <?> msg,
                 direct0= direct0 p <?> msg,
                 direct1= direct1 p <?> msg,
                 indirect= indirect p <?> msg}
   notFollowedBy p = Parser{complete= notFollowedBy (complete p),
                            direct= notFollowedBy (direct p),
                            direct0= notFollowedBy (direct p),
                            direct1= empty,
                            indirect= notFollowedBy (indirect p),
                            cyclicDescendants= \deps-> let (_, nc, nd) = cyclicDescendants p deps in (True, nc, nd)}
   unexpected msg = primitive "unexpected" Nothing (unexpected msg) (unexpected msg)
   skipMany = concatMany . (() <$)

instance MonoidNull s => LookAheadParsing (Parser g s) where
   lookAhead p = Parser{complete= lookAhead (complete p),
                        direct= lookAhead (direct p),
                        direct0= lookAhead (direct p),
                        direct1= empty,
                        indirect= lookAhead (indirect p),
                        cyclicDescendants= \deps-> let (_, nc, nd) = cyclicDescendants p deps in (True, nc, nd)}

instance MonoidParsing (Parser g) where
   endOfInput = primitive "endOfInput" (Just endOfInput) empty endOfInput
   getInput = primitive "getInput" (Just $ eof *> getInput) (notFollowedBy eof *> getInput) getInput
   anyToken = primitive "anyToken" Nothing anyToken anyToken
   token x = primitive "token" Nothing (token x) (token x)
   satisfy predicate = primitive "satisfy" Nothing (satisfy predicate) (satisfy predicate)
   satisfyChar predicate = primitive "satisfyChar" Nothing (satisfyChar predicate) (satisfyChar predicate)
   satisfyCharInput predicate = primitive "satisfyCharInput" Nothing (satisfyCharInput predicate) 
                                          (satisfyCharInput predicate)
   scan s0 f = primitive "scan" (Just $ mempty <$ notSatisfy test) (lookAhead (satisfy test) *> p) p
      where p = scan s0 f
            test = isJust . f s0
   scanChars s0 f = primitive "scanChars" (Just $ mempty <$ notSatisfyChar test) (lookAhead (satisfyChar test) *> p) p
      where p = scanChars s0 f
            test = isJust . f s0
   string s
      | null s = primitive ("(string " ++ shows s ")") (Just $ string s) empty (string s)
      | otherwise = primitive ("(string " ++ shows s ")") Nothing (string s) (string s)
   takeWhile predicate = primitive "takeWhile" (Just $ (mempty <$ notSatisfy predicate))
                                               (takeWhile1 predicate) (takeWhile predicate)
   takeWhile1 predicate = primitive "takeWhile1" Nothing (takeWhile1 predicate) (takeWhile1 predicate)
   takeCharsWhile predicate = primitive "takeCharsWhile" (Just $ mempty <$ notSatisfyChar predicate)
                                                         (takeCharsWhile1 predicate) (takeCharsWhile predicate)
   takeCharsWhile1 predicate = primitive "takeCharsWhile1" Nothing (takeCharsWhile1 predicate)
                                                           (takeCharsWhile1 predicate)
   whiteSpace = primitive "whiteSpace" (Just $ notSatisfyChar isSpace) (satisfyChar isSpace *> whiteSpace) whiteSpace
   concatMany p = Parser{complete= cmp,
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
         cyclicDescendantses = fixCyclicDescendants initial $ Rank2.fmap (Const . cyclicDescendants) g
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
