{-# LANGUAGE FlexibleContexts, GADTs, InstanceSigs, GeneralizedNewtypeDeriving,
             RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeFamilies #-}
{-# OPTIONS -fno-full-laziness #-}
module Text.Grampa.ContextFree.LeftRecursive (Parser)
where

import Control.Applicative
import Control.Arrow((&&&))
import Control.Monad (Monad(..), MonadPlus(..))
import Control.Monad.Trans.State.Lazy (State, evalState, get, put)

import Data.Bool (bool)
import Data.Char (isSpace)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.Maybe (fromMaybe, isJust, maybe)

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet

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

import Prelude hiding (null, showsPrec, span, takeWhile)

data Parser g s a = Parser {
   complete, direct, direct0, direct1, indirect :: Memoizing.Parser g s a,
   nullable' :: g (Const Bool) -> Bool,
--   descendants :: Rank2.Apply g => g (Const Bool),
   cyclicDescendants :: Rank2.Apply g => g (Const (Bool, Bool, g (Const Bool))) -> (Bool, Bool, g (Const Bool)),
   isCyclic :: Bool}

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
--      nullable'= isCyclic . f . Rank2.fmap cyclicToParser,
      cyclicDescendants= cyclicDescendantsF . f . addSelf . Rank2.fmap wrapCyclicDescendants}
      where ind = nonTerminal (resultListF . f . Rank2.fmap wrapResultList)
--            cyclicToParser (Const c) = Parser{isCyclic= c}
            wrapCyclicDescendants (Const cd) = ParserFunctor{cyclicDescendantsF= cd}
            wrapResultList rl = ParserFunctor{resultListF= rl}
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
   pure a = Parser{nullable'= const True,
                   complete= pure a,
                   direct= pure a,
                   direct0= pure a,
                   direct1= empty,
                   indirect= empty,
--                   descendants= Rank2.pure (Const False),
                   cyclicDescendants= \g-> (True, False, const (Const False) Rank2.<$> g),
                   isCyclic= False}
   p <*> q = Parser{nullable'= \nulls-> nullable' p nulls && nullable' q nulls,
                    complete= complete p <*> complete q,
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
   empty = Parser{nullable'= const False,
                  complete= empty,
                  direct= empty,
                  direct0= empty,
                  direct1= empty,
                  indirect= empty,
                  cyclicDescendants= \g-> (False, False, const (Const False) Rank2.<$> g)}
   p <|> q = Parser{nullable'= \nulls-> nullable' p nulls || nullable' q nulls,
                    complete= complete p <|> complete q,
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
   many p = Parser{nullable'= const True,
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
   some p = Parser{nullable'= nullable' p,
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

union (Const False) d = d
union (Const True) _ = Const True

instance Monad (Parser g s) where
   return = pure
   (>>) = (*>)
   p >>= cont = Parser{nullable'= nullable' p,
                       complete= complete p >>= complete . cont,
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
primitive name d0 d1 d = Parser{nullable'= const (isJust d0),
                                complete= d,
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
   notFollowedBy p = Parser{nullable'= const True,
                             complete= notFollowedBy (complete p),
                             direct= notFollowedBy (direct p),
                             direct0= notFollowedBy (direct p),
                             direct1= empty,
                             indirect= notFollowedBy (indirect p),
                             cyclicDescendants= \deps-> let (np, nc, nd) = cyclicDescendants p deps in (True, nc, nd)}
   unexpected msg = primitive "unexpected" Nothing (unexpected msg) (unexpected msg)
   skipMany = concatMany . (() <$)

instance MonoidNull s => LookAheadParsing (Parser g s) where
   lookAhead p = Parser{nullable'= const True,
                         complete= lookAhead (complete p),
                         direct= lookAhead (direct p),
                         direct0= lookAhead (direct p),
                         direct1= empty,
                         indirect= lookAhead (indirect p),
                         cyclicDescendants= \deps-> let (np, nc, nd) = cyclicDescendants p deps in (True, nc, nd)}

instance MonoidParsing (Parser g) where
   endOfInput = primitive "endOfInput" (Just endOfInput) empty endOfInput
   getInput = primitive "getInput" (Just $ eof *> getInput) (notFollowedBy eof *> getInput) getInput
   anyToken = primitive "anyToken" Nothing anyToken anyToken
   token x = primitive "token" Nothing (token x) (token x)
   satisfy predicate = primitive "satisfy" Nothing (satisfy predicate) (satisfy predicate)
   satisfyChar predicate = primitive "satisfyChar" Nothing (satisfyChar predicate) (satisfyChar predicate)
   satisfyCharInput predicate = primitive "satisfyCharInput" Nothing (satisfyCharInput predicate) 
                                          (satisfyCharInput predicate)
   scan s0 f = primitive "scan" (Just $ mempty <$ notFollowedBy (() <$ p1)) (lookAhead p1 *> p) p
      where p = scan s0 f
            p1 = satisfy (isJust . f s0)
   scanChars s0 f = primitive "scanChars" (Just $ mempty <$ notFollowedBy p1) (lookAhead p1 *> p) p
      where p = scanChars s0 f
            p1 = satisfyChar (isJust . f s0)
   string s
      | null s = primitive ("(string " ++ shows s ")") (Just $ string s) empty (string s)
      | otherwise = primitive ("(string " ++ shows s ")") Nothing (string s) (string s)
   takeWhile predicate = primitive "takeWhile" (Just $ mempty <$ notFollowedBy (() <$ satisfy predicate))
                                               (takeWhile1 predicate) (takeWhile predicate)
   takeWhile1 predicate = primitive "takeWhile1" Nothing (takeWhile1 predicate) (takeWhile1 predicate)
   takeCharsWhile predicate = primitive "takeCharsWhile" (Just $ mempty <$ notFollowedBy (satisfyChar predicate))
                                                         (takeCharsWhile1 predicate) (takeCharsWhile predicate)
   takeCharsWhile1 predicate = primitive "takeCharsWhile1" Nothing (takeCharsWhile1 predicate)
                                                           (takeCharsWhile1 predicate)
   whiteSpace = primitive "whiteSpace" (Just $ notFollowedBy $ satisfyChar isSpace) (satisfyChar isSpace *> whiteSpace)
                                       whiteSpace
   concatMany p = Parser{nullable'= const True,
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
{-
         cycles :: g (Const Bool)
         isCyclic :: Const (Bool, Bool, g (Const Bool)) x -> Const Bool x
         isCyclic (Const (_, c, _)) = Const c
         cycles = Rank2.fmap isCyclic cyclicDescendantses
         -- directs = Rank2.fmap direct g
         -- indirects = Rank2.fmap indirect g
         completes = Rank2.fmap complete g
         cond (Const False) _t f = f
         cond (Const True) t _f = t
-}

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

data AST g s a where
   NonTerminal   :: (g (AST g s) -> AST g s a) -> AST g s a
   Primitive     :: String -> Maybe (Memoizing.Parser g s a) -> Maybe (Memoizing.Parser g s a)
                 -> Memoizing.Parser g s a -> AST g s a
   Recursive     :: AST g s a -> AST g s a
   Map           :: (a -> b) -> AST g s a -> AST g s b
   Ap            :: AST g s (a -> b) -> AST g s a -> AST g s b
   Pure          :: a -> AST g s a
   Empty         :: AST g s a
   Bind          :: AST g s a -> (a -> AST g s b) -> AST g s b
   Choice        :: AST g s a -> AST g s a -> AST g s a
   Try           :: AST g s a -> AST g s a
   Describe      :: AST g s a -> String -> AST g s a
   NotFollowedBy :: Show a => AST g s a -> AST g s ()
   Lookahead     :: AST g s a -> AST g s a
   Many          :: AST g s a -> AST g s [a]
   Some          :: AST g s a -> AST g s [a]
   ConcatMany    :: Monoid a => AST g s a -> AST g s a
   ResultsWrap   :: ResultList g s a -> AST g s a
   Index         :: Int -> AST g s a

-- | Parser of general context-free grammars, including left recursion.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Apply' g, "Rank2".'Rank2.Traversable' g, 'FactorialMonoid' s) =>
--                  g (LeftRecursive.'Parser' g s) -> s -> g ('Compose' 'ParseResults' [])
-- @
instance MultiParsing AST where
   type GrammarConstraint AST g = (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g)
   type ResultFunctor AST = Compose ParseResults []
   parsePrefix :: (Rank2.Apply g, Rank2.Traversable g, FactorialMonoid s) =>
                  g (AST g s) -> s -> g (Compose (Compose ParseResults []) ((,) s))
   parsePrefix g input = Rank2.fmap (Compose . Compose . fromResultList input)
                                    (snd $ head $ parseRecursiveAST g input)
   parseComplete :: (FactorialMonoid s, Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g) =>
                    g (AST g s) -> s -> g (Compose ParseResults [])
   parseComplete g input = Rank2.fmap ((snd <$>) . Compose . fromResultList input)
                                      (snd $ head $ Memoizing.reparseTails close $ parseRecursiveAST g input)
      where close = Rank2.fmap (<* endOfInput) selfReferring

instance GrammarParsing AST where
   type GrammarFunctor AST = AST
   nonTerminal = NonTerminal
   recursive = Recursive

instance (Rank2.Distributive g, Rank2.Traversable g) => Show (AST g s a) where
   show (NonTerminal accessor) = "nt" ++ show i
      where Index i = accessor orderedSelfReferring
   show (Primitive name _ _ _) = name
   show Recursive{} = "recursive"
   show (Map _ ast) = "(f <$> " ++ shows ast ")"
   show (Ap f p) = "(" ++ show f ++ " <*> " ++ shows p ")"
   show (Pure _) = "pure x"
   show Empty = "empty"
   show (Bind ast _) = "(" ++ show ast ++ " >>= " ++ ")"
   show (Choice l r) = "(" ++ show l ++ " <|> " ++ shows r ")"
   show (Try ast) = "(try " ++ shows ast ")"
   show (Describe ast msg) = "(" ++ shows ast (" <?> " ++ shows msg ")")
   show (NotFollowedBy ast) = "(notFollowedBy " ++ shows ast ")"
   show (Lookahead ast) = "(lookAhead " ++ shows ast ")"
   show (Many ast) = "(many " ++ shows ast ")"
   show (Some ast) = "(some " ++ shows ast ")"
   show (ConcatMany ast) = "(concatMany " ++ shows ast ")"
   show Index{} = error "Index should be temporary only"
   show ResultsWrap{} = error "ResultsWrap should be temporary only"

instance (Rank2.Distributive g, Rank2.Traversable g) => Show1 (AST g s) where
   liftShowsPrec _showsPrec _showList _prec (NonTerminal accessor) _rest = "nt" ++ show i
      where Index i = accessor orderedSelfReferring
   liftShowsPrec _showsPrec _showL _prec (Primitive name _ _ _) rest = name ++ rest
   liftShowsPrec _showsPrec _showL _prec Recursive{} rest = "recursive" ++ rest
   liftShowsPrec _showsPrec _showL _prec (Map _ ast) rest = "(f <$> " ++ shows ast (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (Ap f p) rest = "(" ++ show f ++ " <*> " ++ shows p (")" ++ rest)
   liftShowsPrec  showsPrec _showL  prec (Pure x) rest = "pure " ++ showsPrec prec x rest
   liftShowsPrec _showsPrec _showL _prec Empty _rest = "empty"
   liftShowsPrec _showsPrec _showL _prec (Bind ast _) rest = "(" ++ shows ast (" >>= " ++ ")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (Choice l r) rest = "(" ++ show l ++ " <|> " ++ shows r (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (Try ast) rest = "(try " ++ shows ast (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (Describe ast msg) rest = "(" ++ shows ast (" <?> " ++ shows msg (")" ++ rest))
   liftShowsPrec _showsPrec _showL _prec (NotFollowedBy ast) rest = "(notFollowedBy " ++ shows ast (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (Lookahead ast) rest = "(lookAhead " ++ shows ast (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (Many ast) rest = "(many " ++ shows ast (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (Some ast) rest = "(some " ++ shows ast (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (ConcatMany ast) rest = "(concatMany " ++ shows ast (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec Index{} _rest = error "Index should be temporary only"
   liftShowsPrec _showsPrec _showL _prec ResultsWrap{} _rest = error "ResultsWrap should be temporary only"

instance Functor (AST g s) where
   fmap _ Empty = Empty
   fmap f ast = Map f ast

instance Applicative (AST g s) where
   pure = Pure
   Empty <*> _ = Empty
   _ <*> Empty = Empty
   p <*> q = Ap p q

instance Alternative (AST g s) where
   empty = Empty
   Empty <|> ast = ast
   ast <|> Empty = ast
   p <|> q = Choice p q
   many Empty = pure []
   many ast = Many ast
   some Empty = Empty
   some ast = Some ast

instance Monad (AST g s) where
   return = pure
   (>>) = (*>)
   Empty >>= _ = Empty
   ast >>= cont = Bind ast cont

instance MonadPlus (AST g s) where
   mzero = empty
   mplus = (<|>)

instance Monoid x => Monoid (AST g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

instance MonoidNull s => Parsing (AST g s) where
   eof = Primitive "eof" (Just eof) Nothing eof
   try Empty = Empty
   try ast = Try ast
   Empty <?> _ = Empty
   ast <?> msg = Describe ast msg
   notFollowedBy = NotFollowedBy
   unexpected msg = Primitive "unexpected" Nothing (Just $ unexpected msg) (unexpected msg)
   skipMany = ConcatMany . (() <$)

instance MonoidNull s => LookAheadParsing (AST g s) where
   lookAhead = Lookahead

instance (Show s, TextualMonoid s) => CharParsing (AST g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Show s, TextualMonoid s) => TokenParsing (AST g s) where
   someSpace = () <$ takeCharsWhile1 isSpace

instance MonoidParsing (AST g) where
   endOfInput = Primitive "endOfInput" (Just endOfInput) Nothing endOfInput
   getInput = Primitive "getInput" (Just $ eof *> getInput) (Just $ notFollowedBy eof *> getInput) getInput
   anyToken = Primitive "anyToken" Nothing (Just anyToken) anyToken
   token x = Primitive "token" Nothing (Just $ token x) (token x)
   satisfy predicate = Primitive "satisfy" Nothing (Just $ satisfy predicate) (satisfy predicate)
   satisfyChar predicate = Primitive "satisfyChar" Nothing (Just $ satisfyChar predicate) (satisfyChar predicate)
   satisfyCharInput predicate = Primitive "satisfyCharInput" Nothing (Just $ satisfyCharInput predicate) 
                                          (satisfyCharInput predicate)
   scan s0 f = Primitive "scan" (Just $ mempty <$ notFollowedBy (() <$ p1)) (Just $ lookAhead p1 *> p) p
      where p = scan s0 f
            p1 = satisfy (isJust . f s0)
   scanChars s0 f = Primitive "scanChars" (Just $ mempty <$ notFollowedBy p1) (Just $ lookAhead p1 *> p) p
      where p = scanChars s0 f
            p1 = satisfyChar (isJust . f s0)
   string s
      | null s = Primitive ("(string " ++ shows s ")") (Just $ string s) Nothing (string s)
      | otherwise = Primitive ("(string " ++ shows s ")") Nothing (Just $ string s) (string s)
   takeWhile predicate = Primitive "takeWhile" (Just $ mempty <$ notFollowedBy (() <$ satisfy predicate))
                                               (Just $ takeWhile1 predicate) (takeWhile predicate)
   takeWhile1 predicate = Primitive "takeWhile1" Nothing (Just $ takeWhile1 predicate) (takeWhile1 predicate)
   takeCharsWhile predicate = Primitive "takeCharsWhile" (Just $ mempty <$ notFollowedBy (satisfyChar predicate))
                                                         (Just $ takeCharsWhile1 predicate) (takeCharsWhile predicate)
   takeCharsWhile1 predicate = Primitive "takeCharsWhile1" Nothing (Just $ takeCharsWhile1 predicate)
                                                           (takeCharsWhile1 predicate)
   whiteSpace = Primitive "whiteSpace" (Just $ notFollowedBy whiteSpace) (Just whiteSpace) whiteSpace
   concatMany = ConcatMany

toParser :: (Rank2.Functor g, FactorialMonoid s) => AST g s a -> Memoizing.Parser g s a
toParser (NonTerminal accessor) = nonTerminal (unwrap . accessor . Rank2.fmap ResultsWrap)
   where unwrap (ResultsWrap x) = x
         unwrap _ = error "should have been wrapped"
toParser (Primitive _ _ _ p) = p
toParser (Recursive ast) = toParser ast
toParser (Map f ast) = f <$> toParser ast
toParser (Ap f a) = toParser f <*> toParser a
toParser (Pure x) = pure x
toParser Empty = empty
toParser (Bind ast cont) = toParser ast >>= toParser . cont
toParser (Choice l r) = toParser l <|> toParser r
toParser (Try ast) = try (toParser ast)
toParser (Describe ast msg) = toParser ast <?> msg
toParser (NotFollowedBy ast) = notFollowedBy (toParser ast)
toParser (Lookahead ast) = lookAhead (toParser ast)
toParser (Many ast) = many (toParser ast)
toParser (Some ast) = some (toParser ast)
toParser (ConcatMany ast) = concatMany (toParser ast)
toParser Index{} = error "Index should be temporary only"
toParser ResultsWrap{} = error "ResultsWrap should be temporary only"

splitDirect :: (Rank2.Functor g, FactorialMonoid s) => AST g s a -> (AST g s a, AST g s a)
splitDirect ast@NonTerminal{} = (empty, ast)
splitDirect ast@Primitive{} = (ast, empty)
splitDirect (Recursive ast) = both Recursive (splitDirect ast)
splitDirect (Map f ast) = both (f <$>) (splitDirect ast)
splitDirect (Ap f a)
   | Empty <- an = (fd <*> a, fn <*> a)
   | otherwise = (fd0 <*> ad <|> fd1 <*> a, fd0 <*> an <|> fn <*> a)
   where (fd, fn) = splitDirect f
         (ad, an) = splitDirect a
         (fd0, fd1) = splitNullable fd
splitDirect ast@Pure{} = (ast, empty)
splitDirect Empty = (Empty, Empty)
splitDirect (Bind ast cont) = (d0cd <|> (d1 >>= cont), d0cn <|> (n >>= cont))
   where (d, n) = splitDirect ast
         (d0, d1) = splitNullable d
         (d0cd, d0cn) = splitDirect (d0 >>= cont)
splitDirect (Choice l r) = (ld <|> rd, ln <|> rn)
   where (ld, ln) = splitDirect l
         (rd, rn) = splitDirect r
splitDirect (Try ast) = both try (splitDirect ast)
splitDirect (Describe ast msg) = both (<?> msg) (splitDirect ast)
splitDirect (NotFollowedBy ast) = both notFollowedBy (splitDirect ast)
splitDirect (Lookahead ast) = both lookAhead (splitDirect ast)
splitDirect ast@(Many ast1) = (pure [] <|> (:) <$> d <*> ast, (:) <$> n <*> ast)
   where (d, n) = splitDirect ast1
splitDirect (Some ast) = ((:) <$> d <*> ast', (:) <$> n <*> ast')
   where (d, n) = splitDirect ast
         ast' = Many ast
splitDirect ast@(ConcatMany ast1) = (pure mempty <|> (<>) <$> d <*> ast, (<>) <$> n <*> ast)
   where (d, n) = splitDirect ast1
splitDirect Index{} = error "Index should be temporary only"
splitDirect ResultsWrap{} = error "ResultsWrap should be temporary only"

splitNullable :: MonoidNull s => AST g s a -> (AST g s a, AST g s a)
splitNullable ast@NonTerminal{} = (ast, empty)
splitNullable (Primitive name p0 p1 _) = (maybe empty (\p-> Primitive name (Just p) Nothing p) p0,
                                          maybe empty (\p-> Primitive name Nothing (Just p) p) p1)
splitNullable (Recursive ast) = both Recursive (splitNullable ast)
splitNullable (Map f ast) = both (f <$>) (splitNullable ast)
splitNullable (Ap f a)
   | Empty <- f0 = (empty, f <*> a)
   | Empty <- a0 = (empty, f <*> a)
   | otherwise = (f0 <*> a0, f1 <*> a <|> f <*> a1)
   where (f0, f1) = splitNullable f
         (a0, a1) = splitNullable a
splitNullable ast@Pure{} = (ast, empty)
splitNullable Empty = (empty, empty)
splitNullable (Bind ast cont) = (fst c0, snd c0 <|> (ast1 >>= cont))
   where (ast0, ast1) = splitNullable ast
         c0 = splitNullable (ast0 >>= cont)
splitNullable (Choice l r) = (l0 <|> r0, l1 <|> r1)
   where (l0, l1) = splitNullable l
         (r0, r1) = splitNullable r
splitNullable (Try ast) = both try (splitNullable ast)
splitNullable (Describe ast msg) = both (<?> msg) (splitNullable ast)
splitNullable ast@NotFollowedBy{} = (ast, empty)
splitNullable ast@Lookahead{} = (ast, empty)
splitNullable (Many ast) = (pure [] <|> (:[]) <$> ast0, (:) <$> ast1 <*> many ast)
   where (ast0, ast1) = splitNullable ast
splitNullable (Some ast) = ((:[]) <$> ast0, (:) <$> ast1 <*> many ast)
   where (ast0, ast1) = splitNullable ast
splitNullable (ConcatMany ast) = (pure mempty <|> ast0, (<>) <$> ast1 <*> concatMany ast)
   where (ast0, ast1) = splitNullable ast
splitNullable (ResultsWrap _) = error "ResultsWrap should be temporary only"
splitNullable (Index _) = error "Index should be temporary only"

both :: (a -> b) -> (a, a) -> (b, b)
both f (x, y) = (f x, f y)

leftDescendants :: forall g s. (Rank2.Apply g, Rank2.Traversable g) => g (AST g s) -> g (Const (Bool, g (Const Bool)))
leftDescendants g = evalState (Rank2.traverse (const replaceFromList) g) $ map (setToBools <$>) $
                    IntMap.elems $ calcLeftSets $ IntMap.fromList $ zip [0..] $ Rank2.foldMap successorSet g
   where replaceFromList :: State [x] (Const x y)
         replaceFromList = do next:rest <- get
                              put rest
                              return (Const next)
         setToBools :: IntSet -> g (Const Bool)
         setToBools = Rank2.traverse isElem enumeration
         isElem :: AST g s a -> IntSet -> Const Bool a
         isElem (Index i) set = Const (IntSet.member i set)
         successorSet :: AST g s a -> [IntSet]
         successorSet a = [leftRecursiveOn a]
         enumeration = ordered g
         universe = Rank2.foldMap (\(Index i)-> IntSet.singleton i) enumeration
         g0 = fixNullable g
         leftRecursiveOn :: AST g s a -> IntSet
         leftRecursiveOn (NonTerminal accessor) = IntSet.singleton i
            where Index i = accessor enumeration
         leftRecursiveOn Primitive{} = mempty
         leftRecursiveOn (Recursive ast) = leftRecursiveOn ast
         leftRecursiveOn (Map _ ast) = leftRecursiveOn ast
         leftRecursiveOn (Ap f p) = leftRecursiveOn f <> if nullable g0 f then leftRecursiveOn p else mempty
         leftRecursiveOn Pure{} = mempty
         leftRecursiveOn Empty = mempty
         leftRecursiveOn (Bind ast _cont) = if nullable g0 ast then universe else leftRecursiveOn ast
         leftRecursiveOn (Choice l r) = leftRecursiveOn l <> leftRecursiveOn r
         leftRecursiveOn (Try ast) = leftRecursiveOn ast
         leftRecursiveOn (Describe ast _) = leftRecursiveOn ast
         leftRecursiveOn (NotFollowedBy ast) = leftRecursiveOn ast
         leftRecursiveOn (Lookahead ast) = leftRecursiveOn ast
         leftRecursiveOn (Many ast) = leftRecursiveOn ast
         leftRecursiveOn (Some ast) = leftRecursiveOn ast
         leftRecursiveOn (ConcatMany ast) = leftRecursiveOn ast

nullable :: Rank2.Functor g => g (Const Bool) -> AST g s a -> Bool
nullable gn (NonTerminal accessor) = n == 1
   where Index n = accessor (Rank2.fmap (\(Const z)-> Index $ if z then 1 else 0) gn)
nullable _  (Primitive _name z _ _) = isJust z
nullable gn (Recursive ast) = nullable gn ast
nullable gn (Map _ ast) = nullable gn ast
nullable gn (Ap f p) = nullable gn f && nullable gn p
nullable _  Pure{} = True
nullable _  Empty = False
nullable gn (Bind ast _cont) = nullable gn ast
nullable gn (Choice l r) = nullable gn l || nullable gn r
nullable gn (Try ast) = nullable gn ast
nullable gn (Describe ast _) = nullable gn ast
nullable _  NotFollowedBy{} = True
nullable _  Lookahead{} = True
nullable _  Many{} = True
nullable gn (Some ast) = nullable gn ast
nullable _  ConcatMany{} = True

fixNullable :: (Rank2.Apply g, Rank2.Foldable g) => g (AST g s) -> g (Const Bool)
fixNullable g = go (Rank2.fmap (const $ Const True) g)
   where go gn
            | getAll (Rank2.foldMap (All . getConst) $ Rank2.liftA2 agree gn gn') = gn
            | otherwise = go gn'
            where gn' = Rank2.fmap (Const . nullable gn) g
         agree x y = Const (x == y)

orderedSelfReferring :: (Rank2.Distributive g, Rank2.Traversable g) => g (AST g s)
orderedSelfReferring = ordered (Rank2.distributeWith NonTerminal id)

ordered :: Rank2.Traversable g => g (AST g s) -> g (AST g s)
ordered g = evalState (Rank2.traverse (const increment) g) 0
   where increment :: State Int (AST g s a)
         increment = do {n <- get; put (n+1); return (Index n)}

data AdvanceFront = AdvanceFront{visited       :: IntSet,
                                 cyclic        :: Bool,
                                 front         :: IntSet}
                  deriving Show

calcLeftSets :: IntMap IntSet -> IntMap (Bool, IntSet)
calcLeftSets successors = (cyclic &&& visited) <$> expandPaths initialDepths
   where expandPaths :: IntMap AdvanceFront -> IntMap AdvanceFront
         expandPaths paths
            | all (IntSet.null . front) paths' = paths'
            | otherwise = expandPaths paths'
            where paths' = expandReachables <$> paths
                  expandReachables :: AdvanceFront -> AdvanceFront
                  expandReachables x = 
                     AdvanceFront{visited= visited x <> front x,
                                  cyclic= cyclic x || not (IntSet.null $ IntSet.intersection (front x) (visited x)),
                                  front= IntSet.foldr' addSuccessors mempty (IntSet.difference (front x) (visited x))}
         addSuccessors :: Int -> IntSet -> IntSet
         addSuccessors node set = set <> successors IntMap.! node
         initialDepths = IntMap.mapWithKey setToFront successors
         setToFront root set = AdvanceFront{visited= mempty,
                                            cyclic= IntSet.member root set,
                                            front= set}

newtype Couple f a = Couple{unCouple :: (f a, f a)} deriving Show

parseRecursiveAST :: forall g s. (Rank2.Apply g, Rank2.Traversable g, FactorialMonoid s) =>
                     g (AST g s) -> s -> [(s, g (ResultList g s))]
parseRecursiveAST ast = parseSeparated descendants (Rank2.fmap toParser indirect) (Rank2.fmap toParser direct)
   where directRecursive = Rank2.fmap (Couple . splitDirect) ast
         cyclicDescendants = leftDescendants ast
         cyclic = Rank2.fmap (mapConst fst) cyclicDescendants
         descendants = Rank2.liftA3 cond cyclic (Rank2.fmap (mapConst snd) cyclicDescendants) noDescendants
         direct = Rank2.liftA3 cond cyclic (Rank2.fmap (fst . unCouple) directRecursive) ast
         indirect = Rank2.liftA3 cond cyclic (Rank2.fmap (snd . unCouple) directRecursive) emptyGrammar
         emptyGrammar :: g (AST g s)
         emptyGrammar = Rank2.fmap (const empty) ast
         noDescendants = Rank2.fmap (const $ Const $ Rank2.fmap (const $ Const False) ast) ast
         cond (Const False) _t f = f
         cond (Const True) t _f = t
         mapConst f (Const c) = Const (f c)

-- | Parse the given input using a context-free grammar separated into two parts: the first specifying all the
-- left-recursive productions, the second all others. The first function argument specifies the left-recursive
-- dependencies among the grammar productions.
parseSeparated :: forall g s. (Rank2.Apply g, Rank2.Foldable g, FactorialMonoid s) =>
                  g (Const (g (Const Bool))) -> g (Memoizing.Parser g s) -> g (Memoizing.Parser g s) -> s
               -> [(s, g (ResultList g s))]
parseSeparated dependencies indirect direct input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d'):parsedTail
                  d      = Rank2.fmap (($ (s,d):parsedTail) . Memoizing.applyParser) direct
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

         recurseOnce s parsedTail initial = Rank2.fmap (($ parsed) . Memoizing.applyParser) indirect
            where parsed = (s, initial):parsedTail
