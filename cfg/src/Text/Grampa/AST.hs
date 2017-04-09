{-# LANGUAGE FlexibleContexts, GADTs, InstanceSigs, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeFamilies #-}
{-# OPTIONS -fno-full-laziness #-}
module Text.Grampa.AST (AST(..), Grammar, 
                        fixGrammarAST, fixNullable, leftDescendants, nullable, splitDirect, splitNullable, toParser)
where

import Control.Applicative
import Control.Arrow((&&&))
import Control.Monad (Monad(..), MonadPlus(..))
import Control.Monad.Trans.State.Lazy (State, evalState, get, put)

import Data.Functor.Classes (Show1(..))
import Data.Maybe (fromMaybe, isJust, maybe)
import Data.Monoid (All(..), Any(..), (<>))
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet

import Data.Monoid (Monoid(mempty), (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Textual as Textual
import Data.String (fromString)

import qualified Text.Parser.Char
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))

import qualified Rank2
import Text.Grampa.Class (GrammarParsing(..), MonoidParsing(..), RecursiveParsing(..))
import Text.Grampa.Parser (Parser(..), ResultList)

import Prelude hiding (iterate, null, showsPrec, span, takeWhile)

type Grammar g s = g (AST g s)

data AST g s a where
   NonTerminal   :: (g (AST g s) -> AST g s a) -> AST g s a
   Primitive     :: String -> Maybe (Parser g s a) -> Maybe (Parser g s a) -> Parser g s a -> AST g s a
   Recursive     :: AST g s a -> AST g s a
   Map           :: (a -> b) -> AST g s a -> AST g s b
   Ap            :: AST g s (a -> b) -> AST g s a -> AST g s b
   Pure          :: a -> AST g s a
   Empty         :: AST g s a
   Bind          :: AST g s a -> (a -> AST g s b) -> AST g s b
   Choice        :: AST g s a -> AST g s a -> AST g s a
   BiasedChoice  :: AST g s a -> AST g s a -> AST g s a
   Try           :: AST g s a -> AST g s a
   Describe      :: AST g s a -> String -> AST g s a
   NotFollowedBy :: Show a => AST g s a -> AST g s ()
   Lookahead     :: AST g s a -> AST g s a
   Many          :: AST g s a -> AST g s [a]
   Some          :: AST g s a -> AST g s [a]
   ConcatMany    :: Monoid a => AST g s a -> AST g s a
   ResultsWrap   :: ResultList g s a -> AST g s a
   Index         :: Int -> AST g s a

instance (Rank2.Distributive g, Rank2.Traversable g) => Show (AST g s a) where
   show (NonTerminal accessor) = "nt" ++ show i
      where Index i = accessor (ordered selfReferring)
   show (Primitive name _ _ _) = name
   show Recursive{} = "recursive"
   show (Map _ ast) = "(f <$> " ++ shows ast ")"
   show (Ap f p) = "(" ++ show f ++ " <*> " ++ shows p ")"
   show (Pure _) = "pure x"
   show Empty = "empty"
   show (Bind ast _) = "(" ++ show ast ++ " >>= " ++ ")"
   show (Choice l r) = "(" ++ show l ++ " <|> " ++ shows r ")"
   show (BiasedChoice l r) = "(" ++ show l ++ " <<|> " ++ shows r ")"
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
   liftShowsPrec _showsPrec _showList _prec (NonTerminal accessor) rest = "nt" ++ show i
      where Index i = accessor (ordered selfReferring)
   liftShowsPrec _showsPrec _showL _prec (Primitive name _ _ _) rest = name ++ rest
   liftShowsPrec _showsPrec _showL _prec Recursive{} rest = "recursive" ++ rest
   liftShowsPrec _showsPrec _showL _prec (Map _ ast) rest = "(f <$> " ++ shows ast (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (Ap f p) rest = "(" ++ show f ++ " <*> " ++ shows p (")" ++ rest)
   liftShowsPrec  showsPrec _showL  prec (Pure x) rest = "pure " ++ showsPrec prec x rest
   liftShowsPrec _showsPrec _showL _prec Empty rest = "empty"
   liftShowsPrec _showsPrec _showL _prec (Bind ast _) rest = "(" ++ shows ast (" >>= " ++ ")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (Choice l r) rest = "(" ++ show l ++ " <|> " ++ shows r (")" ++ rest)
   liftShowsPrec _showsPrec _showL _prec (BiasedChoice l r) rest = "(" ++ show l ++ " <<|> " ++ shows r (")" ++ rest)
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
   eof = endOfInput
   try Empty = Empty
   try ast = Try ast
   Empty <?> _ = Empty
   ast <?> msg = Describe ast msg
   notFollowedBy = NotFollowedBy
   unexpected msg = Primitive "unexpected" Nothing (Just $ unexpected msg) (unexpected msg)
   skipMany = ConcatMany . (() <$)

instance MonoidNull s => LookAheadParsing (AST g s) where
   lookAhead = Lookahead

instance (Show s, TextualMonoid s) => Text.Parser.Char.CharParsing (AST g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance GrammarParsing AST where
   type GrammarFunctor AST = AST
   nonTerminal = NonTerminal

instance MonoidNull s => RecursiveParsing (AST g s) where
   recursive = Recursive

instance MonoidParsing (AST g) where
   (<<|>) = BiasedChoice
   endOfInput = Primitive "endOfInput" (Just endOfInput) Nothing endOfInput
   getInput = Primitive "getInput" (Just $ endOfInput *> getInput) (Just $ notFollowedBy endOfInput *> getInput) getInput
   anyToken = Primitive "anyToken" Nothing (Just anyToken) anyToken
   token x = Primitive "token" Nothing (Just $ token x) (token x)
   satisfy predicate = Primitive "satisfy" Nothing (Just $ satisfy predicate) (satisfy predicate)
   satisfyChar predicate = Primitive "satisfyChar" Nothing (Just $ satisfyChar predicate) (satisfyChar predicate)
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

fixGrammarAST :: forall g s. Rank2.Distributive g => (g (AST g s) -> g (AST g s)) -> g (AST g s)
fixGrammarAST gf = gf selfReferring

selfReferring :: Rank2.Distributive g => g (AST g s)
selfReferring = Rank2.distributeWith NonTerminal id

toParser :: (Rank2.Functor g, FactorialMonoid s) => AST g s a -> Parser g s a
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
toParser (BiasedChoice l r) = toParser l <<|> toParser r
toParser (Try ast) = try (toParser ast)
toParser (Describe ast msg) = toParser ast <?> msg
toParser (NotFollowedBy ast) = notFollowedBy (toParser ast)
toParser (Lookahead ast) = lookAhead (toParser ast)
toParser (Many ast) = many (toParser ast)
toParser (Some ast) = some (toParser ast)
toParser (ConcatMany ast) = concatMany (toParser ast)
toParser (ResultsWrap _) = error "ResultsWrap should be temporary only"

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
splitDirect (BiasedChoice l r) = (ld <<|> rd, ln <<|> rn)
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
splitDirect (ResultsWrap _) = error "ResultsWrap should be temporary only"

splitNullable :: MonoidNull s => AST g s a -> (AST g s a, AST g s a)
splitNullable ast@NonTerminal{} = (ast, empty)
splitNullable NonTerminal{} = error "Can't tell if a nonterminal is nullable"
splitNullable ast@(Primitive name p0 p1 _) = (maybe empty (\p-> Primitive name (Just p) Nothing p) p0,
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
splitNullable (BiasedChoice l r) = (l0 <<|> r0, l1 <<|> r1)
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
leftDescendants g = evalState (Rank2.traverse addDepth g) $
                    IntMap.elems $ calcLeftSets $ IntMap.fromList $ zip [0..] $ Rank2.foldMap successorSet g
   where addDepth :: AST g s a -> State [(Bool, IntSet)] (Const (Bool, g (Const Bool)) a)
         addDepth a = do (cyclic, descendants):rest <- get
                         put rest
                         return (Const (cyclic, setToBools descendants))
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
         leftRecursiveOn (Map f ast) = leftRecursiveOn ast
         leftRecursiveOn (Ap f p) = leftRecursiveOn f <> if nullable g0 f then leftRecursiveOn p else mempty
         leftRecursiveOn (Pure a) = mempty
         leftRecursiveOn Empty = mempty
         leftRecursiveOn (Bind ast cont) = if nullable g0 ast then universe else leftRecursiveOn ast
         leftRecursiveOn (Choice l r) = leftRecursiveOn l <> leftRecursiveOn r
         leftRecursiveOn (BiasedChoice l r) = leftRecursiveOn l <> leftRecursiveOn r
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
nullable _  (Pure a) = True
nullable _  Empty = False
nullable gn (Bind ast cont) = nullable gn ast
nullable gn (Choice l r) = nullable gn l || nullable gn r
nullable gn (BiasedChoice l r) = nullable gn l || nullable gn r
nullable gn (Try ast) = nullable gn ast
nullable gn (Describe ast _) = nullable gn ast
nullable _  (NotFollowedBy ast) = True
nullable _  (Lookahead ast) = True
nullable _  (Many ast) = True
nullable gn (Some ast) = nullable gn ast
nullable _  (ConcatMany ast) = True

fixNullable :: (Rank2.Apply g, Rank2.Foldable g) => g (AST g s) -> g (Const Bool)
fixNullable g = go (Rank2.fmap (const $ Const True) g)
   where go gn
            | getAll (Rank2.foldMap (All . getConst) $ Rank2.liftA2 agree gn gn') = gn
            | otherwise = go gn'
            where gn' = Rank2.fmap (Const . nullable gn) g
         agree x y = Const (x == y)

ordered :: Rank2.Traversable g => g (AST g s) -> g (AST g s)
ordered g = evalState (Rank2.traverse f g) 0
   where f :: AST g s a -> State Int (AST g s a)
         f a = do {n <- get; put (n+1); return (Index n)}

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
                                  front= IntSet.foldr' advance mempty (IntSet.difference (front x) (visited x))}
         advance :: Int -> IntSet -> IntSet
         advance node front = front <> successors IntMap.! node
         initialDepths = IntMap.mapWithKey setToFront successors
         setToFront root set = AdvanceFront{visited= mempty,
                                            cyclic= IntSet.member root set,
                                            front= set}
