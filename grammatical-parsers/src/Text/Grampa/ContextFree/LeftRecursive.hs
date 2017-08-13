{-# LANGUAGE FlexibleContexts, GADTs, InstanceSigs, GeneralizedNewtypeDeriving,
             RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS -fno-full-laziness #-}
module Text.Grampa.ContextFree.LeftRecursive (Parser(..), parseSeparated, fixCyclicDescendants, cyclicDescendants, general, separated, ParserFlags(..))
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

import Prelude hiding (cycle, null, span, takeWhile)

data Parser g s a =
   Parser {
      complete, direct, direct0, direct1, indirect :: Memoizing.Parser g s a,
      cyclicDescendants :: Rank2.Apply g => g (Const (ParserFlags g)) -> ParserFlags g}
   | DirectParser {
      complete, direct0, direct1 :: Memoizing.Parser g s a}
   | PositiveDirectParser {
      complete :: Memoizing.Parser g s a}

data SeparatedParser g s a = SeparatedParser {
   front :: Maybe (Memoizing.Parser g s a),
   cycle :: Maybe (Memoizing.Parser g s a, g (Const Bool)),
   back  :: Memoizing.Parser g s a}

instance Show (g (Const Bool)) => Show (SeparatedParser g s a) where
   show sp = "SeparatedParser{\n  front=" ++ show (isJust $ front sp) ++ ",\n  cycle=" ++ shows (snd <$> cycle sp) "}"

data ParserFlags g = ParserFlags {
   nullable :: Bool,
   cyclic :: Bool,
   dependsOn :: g (Const Bool)}

data ParserFunctor g s a = ParserResultsFunctor {parserResults :: ResultList g s a}
                         | ParserFlagsFuntor {parserFlags :: ParserFlags g}
                         | ParserFlagFunctor {parserFlag :: Bool}

newtype Union (g :: (* -> *) -> *) = Union{getUnion :: g (Const Bool)}

--instance Rank2.Applicative g => Monoid (Union g) where
--   mempty = Union (Rank2.pure $ Const False)

instance (Rank2.Apply g, Rank2.Distributive g) => Monoid (Union g) where
   mempty = Union (Rank2.distributeWith (Const . getConst) (Const False))
   mappend (Union g1) (Union g2) = Union (Rank2.liftA2 union g1 g2)

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
   cyclicDescendants= \cd-> ParserFlags False False (const (Const False) Rank2.<$> cd)}
general' p@DirectParser{} = Parser{
   complete= complete p,
   direct = complete p,
   direct0= direct0 p,
   direct1= direct1 p,
   indirect= empty,
   cyclicDescendants= \cd-> ParserFlags True False (const (Const False) Rank2.<$> cd)}
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
   parsePrefix :: (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g, FactorialMonoid s) =>
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
      cyclicDescendants= parserFlags . f . Rank2.fmap (ParserFlagsFuntor . getConst) . addSelf}
      where ind = nonTerminal (parserResults . f . Rank2.fmap ParserResultsFunctor)
            addSelf g = Rank2.liftA2 adjust bits g
            adjust :: forall b. Const (g (Const Bool)) b -> Const (ParserFlags g) b -> Const (ParserFlags g) b
            adjust (Const bit) (Const (ParserFlags n c d)) =
               Const ParserFlags{
                  nullable= n, 
                  cyclic= parserFlag (f $ Rank2.fmap (ParserFlagFunctor . getConst) d),
                  dependsOn= Rank2.liftA2 union bit d}
   recursive = general

bits :: forall (g :: (* -> *) -> *). (Rank2.Distributive g, Rank2.Traversable g) => g (Const (g (Const Bool)))
bits = start `seq` Rank2.fmap oneBit start
   where start = evalState (Rank2.traverse next (Rank2.distributeJoin Nothing)) 0
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
           pcd@(ParserFlags pn pc pd) = cyclicDescendants p' deps
           ParserFlags qn qc qd = cyclicDescendants q deps
        in if pn
           then ParserFlags qn (pc || qc) (Rank2.liftA2 union pd qd)
           else pcd}
      where p'@Parser{} = general' p
   p <*> q = Parser{
      complete= complete p' <*> complete q',
      direct= direct p' <*> complete q',
      direct0= direct0 p' <*> direct0 q',
      direct1= direct0 p' <*> direct1 q' <|> direct1 p' <*> complete q',
      indirect= indirect p' <*> complete q',
      cyclicDescendants= \deps-> let
           pcd@(ParserFlags pn pc pd) = cyclicDescendants p' deps
           ParserFlags qn qc qd = cyclicDescendants q' deps
        in if pn
           then ParserFlags qn (pc || qc) (Rank2.liftA2 union pd qd)
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
                         ParserFlags pn pc pd = cyclicDescendants p' deps
                         ParserFlags qn qc qd = cyclicDescendants q' deps
                      in ParserFlags (pn || qn) (pc || qc) (Rank2.liftA2 union pd qd)}
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
      cyclicDescendants= \cd-> (ParserFlags True True $ Rank2.fmap (const $ Const True) cd)}
      where d0 = direct0 p >>= direct0 . cont
            d1 = (direct0 p >>= direct1 . general' . cont) <|> (direct1 p >>= complete . cont)

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
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}
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
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}

instance MonoidParsing (Parser g) where
   endOfInput = primitive "endOfInput" endOfInput empty endOfInput
   getInput = primitive "getInput" (eof *> getInput) (notFollowedBy eof *> getInput) getInput
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

instance (Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Show s, TextualMonoid s) => TokenParsing (Parser g s) where
   someSpace = () <$ takeCharsWhile1 isSpace

parseRecursive :: forall g s. (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g, FactorialMonoid s) =>
                  g (Parser g s) -> s -> [(s, g (ResultList g s))]
parseRecursive = parseSeparated . separated

separated :: forall g s. (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g) =>
             g (Parser g s) -> g (SeparatedParser g s)
separated g = Rank2.liftA4 reseparate circulars cycleFollowers (Rank2.fmap (Const . dependsOn . getConst) cyclicDescendantses) g
   where descendants :: g (Const (g (Const Bool)))
         cycleLeaders, cycleFollowers, circulars :: g (Const Bool)
         desc :: forall a. Const Bool a -> Const (ParserFlags g) a -> Const (g (Const Bool)) a
         cyclicDescendantses :: g (Const (ParserFlags g))
         leftRecursive :: forall a. Const (g (Const Bool)) a -> Const (ParserFlags g) a -> Const Bool a
         leftRecursiveLeader :: forall a. Const (ParserFlags g) a -> Const Bool a
         leftRecursiveDeps :: forall a. Const Bool a -> Const (ParserFlags g) a -> Const (g (Const Bool)) a
         reseparate :: forall a. Const Bool a -> Const Bool a -> Const (g (Const Bool)) a -> Parser g s a -> SeparatedParser g s a
         descendants = Rank2.liftA2 desc circulars cyclicDescendantses
         leaders = Rank2.liftA3 leaderOrEmpty cycleLeaders circulars g
         indirects = Rank2.liftA2 indirectOrEmpty circulars g
         directs = Rank2.liftA2 directOrComplete circulars g
         reseparate (Const circular) (Const follower) (Const deps) p
            | circular || leader && follower = SeparatedParser Nothing (Just (indirect p, deps)) (direct p)
            | follower = SeparatedParser Nothing Nothing (complete p)
            | otherwise = SeparatedParser (Just $ complete p) Nothing (error "not used by any cycle")
            where leader = getAny (Rank2.foldMap (Any . getConst) $ Rank2.liftA2 intersection circulars deps)
         leaderOrEmpty (Const leader) (Const circular) p = if leader && not circular then complete p else empty
         indirectOrEmpty (Const circular) p = if circular then indirect p else empty
         directOrComplete (Const circular) p = if circular then direct p else complete p
         desc (Const circular) (Const flags) = Const (if circular then dependsOn flags else falses)
         cyclicDescendantses = fixCyclicDescendants (Rank2.fmap (Const . cyclicDescendants . general) g)
         falses = const (Const False) Rank2.<$> g
         circulars = Rank2.liftA2 leftRecursive bits cyclicDescendantses
         cycleFollowers = getUnion (Rank2.foldMap (Union . getConst) $
                                    Rank2.liftA2 leftRecursiveDeps circulars cyclicDescendantses)
         cycleLeaders = Rank2.fmap leftRecursiveLeader cyclicDescendantses
         leftRecursive (Const bit) (Const flags) =
            Const (getAny $ Rank2.foldMap (Any . getConst) $ Rank2.liftA2 intersection bit $ dependsOn flags)
         leftRecursiveDeps (Const True) (Const flags) = Const (dependsOn flags)
         leftRecursiveDeps (Const False) (Const flags) = Const (Rank2.fmap (const $ Const False) (dependsOn flags))
         leftRecursiveLeader (Const flags) = 
            Const (getAny $ Rank2.foldMap (Any . getConst) $ Rank2.liftA2 intersection circulars $ dependsOn flags)
         intersection (Const a) (Const b) = Const (a && b)

fixCyclicDescendants :: forall g. (Rank2.Apply g, Rank2.Traversable g)
                     => g (Const (g (Const (ParserFlags g)) -> (ParserFlags g))) -> g (Const (ParserFlags g))
fixCyclicDescendants gf = go initial
   where go :: g (Const (ParserFlags g)) -> g (Const (ParserFlags g))
         go cd
            | getAll (Rank2.foldMap (All . getConst) $ Rank2.liftA2 agree cd cd') = cd
            | otherwise = go cd'
            where cd' = Rank2.liftA2 depsUnion cd (Rank2.fmap (\(Const f)-> Const (f cd)) gf)
         agree (Const (ParserFlags xn xc xd)) (Const (ParserFlags yn yc yd)) =
            Const (xn == yn && xc == yc && getAll (Rank2.foldMap (All . getConst) (Rank2.liftA2 agree' xd yd)))
         agree' (Const x) (Const y) = Const (x == y)
         depsUnion (Const ParserFlags{dependsOn= old}) (Const (ParserFlags n c new)) = 
            Const (ParserFlags n c $ if c then Rank2.liftA2 union old new else new)
         initial = const (Const (ParserFlags True False (const (Const False) Rank2.<$> gf))) Rank2.<$> gf

-- | Parse the given input using a context-free grammar separated into two parts: the first specifying all the
-- left-recursive productions, the second all others. The first function argument specifies the left-recursive
-- dependencies among the grammar productions.
parseSeparated :: forall g s. (Rank2.Apply g, Rank2.Foldable g, FactorialMonoid s) =>
                  g (SeparatedParser g s) -> s -> [(s, g (ResultList g s))]
parseSeparated parsers input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d''):parsedTail
                  d      = Rank2.fmap (($ (s,d):parsedTail) . Memoizing.applyParser) directs
                  d'     = fixRecursive s parsedTail d
                  d''    = Rank2.liftA2 f parsers d'
                  f :: forall a. SeparatedParser g s a -> ResultList g s a -> ResultList g s a
                  f sp res = maybe res (($ (s,d''):parsedTail) . Memoizing.applyParser) (front sp)
         fixRecursive :: s -> [(s, g (ResultList g s))] -> g (ResultList g s) -> g (ResultList g s)
         whileAnyContinues :: g (ResultList g s) -> g (ResultList g s) -> g (ResultList g s)
         recurseOnce :: s -> [(s, g (ResultList g s))] -> g (ResultList g s) -> g (ResultList g s)
         maybeDependencies :: g (Const (Maybe (g (Const Bool))))

         directs = Rank2.fmap back parsers
         indirects = Rank2.fmap (maybe empty fst . cycle) parsers
         maybeDependencies = Rank2.fmap (Const . fmap snd . cycle) parsers
                                                                   
         fixRecursive s parsedTail initial =
            foldr1 whileAnyContinues (iterate (recurseOnce s parsedTail) initial)

         -- maybeDependencies = Rank2.fmap (\(Const deps)-> Const (if getAny (Rank2.foldMap (Any . getConst) deps) 
         --                                                        then Just deps else Nothing))
         --                     dependencies

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
