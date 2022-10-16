{-# LANGUAGE ConstraintKinds, CPP, FlexibleContexts, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving, InstanceSigs,
             RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeFamilies, TypeOperators,
             UndecidableInstances #-}
-- | A context-free memoizing parser that can handle left-recursive grammars.
module Text.Grampa.ContextFree.LeftRecursive (Fixed, Parser, SeparatedParser(..),
                                              autochain, longest, peg, terminalPEG,
                                              liftPositive, liftPure, mapPrimitive,
                                              parseSeparated, separated)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..), void)
#if MIN_VERSION_base(4,13,0)
import Control.Monad (MonadFail(fail))
#endif
import Control.Monad.Trans.State.Lazy (State, evalState)
import qualified Control.Monad.Trans.State.Lazy as State

import Data.Functor.Compose (Compose(..))
import Data.Kind (Type)
import Data.Maybe (isJust)

import Data.Semigroup (Semigroup(..))
import Data.Monoid (Monoid(mempty), All(..), Any(..))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)
import Data.Semigroup.Cancellative (LeftReductive)
import qualified Data.Monoid.Factorial as Factorial
import qualified Data.Monoid.Textual as Textual
import Data.String (fromString)
import Data.Type.Equality ((:~:)(Refl))
import Witherable (Filterable(mapMaybe))

import qualified Text.Parser.Char as Char
import Text.Parser.Char (CharParsing)
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))

import qualified Rank2
import Text.Grampa.Class (GrammarParsing(..), InputParsing(..), InputCharParsing(..), MultiParsing(..),
                          AmbiguousParsing(..), CommittedParsing(..), ConsumedInputParsing(..),
                          DeterministicParsing(..),
                          TailsParsing(parseTails, parseAllTails),
                          ParseResults, ParseFailure(..), Pos)
import Text.Grampa.Internal (ResultList(..), FallibleResults(..),
                             AmbiguousAlternative(ambiguousOr), AmbiguityDecidable(..), AmbiguityWitness(..),
                             ParserFlags (ParserFlags, nullable, dependsOn),
                             Dependencies (DynamicDependencies, StaticDependencies),
                             TraceableParsing(..))
import Text.Grampa.Internal.Storable (Storable1(reuse1), Storable11(reuse11, store11))
import qualified Text.Grampa.ContextFree.SortedMemoizing as Memoizing
import qualified Text.Grampa.PEG.Backtrack.Measured as Backtrack

import Prelude hiding (cycle, null, span, take, takeWhile)

-- | A parser for left-recursive grammars
type Parser = Fixed Memoizing.Parser

type ResultAppend p (g :: (Type -> Type) -> Type) s =
   GrammarFunctor (p g s) Rank2.~> GrammarFunctor (p g s) Rank2.~> GrammarFunctor (p g s)

-- | A transformer that adds left-recursive powers to a memoizing parser @p@ over grammar @g@
data Fixed p g s a =
   -- | a fully general parser
   Parser {
      complete, direct, direct0, direct1, indirect :: p g s a,
      choices :: ChoiceTree (Fixed p g s a),
      isAmbiguous :: Maybe (AmbiguityWitness a),
      cyclicDescendants :: g (Const (ParserFlags g)) -> ParserFlags g}
   -- | a parser that doesn't start with a 'nonTerminal'
   | DirectParser {
      complete, direct0, direct1 :: p g s a}
   -- | a parser that doesn't start with a 'nonTerminal' and always consumes some input
   | PositiveDirectParser {
      complete :: p g s a}

-- | Binary tree with two different choice nodes
data ChoiceTree a =
   Leaf a
   | SymmetricChoice (ChoiceTree a) (ChoiceTree a)
   | LeftBiasedChoice (ChoiceTree a) (ChoiceTree a)
   deriving Show

instance Functor ChoiceTree where
  fmap f (Leaf a) = Leaf (f a)
  fmap f (SymmetricChoice a b) = SymmetricChoice (fmap f a) (fmap f b)
  fmap f (LeftBiasedChoice a b) = LeftBiasedChoice (fmap f a) (fmap f b)

instance Foldable ChoiceTree where
  foldMap f (Leaf a) = f a
  foldMap f (SymmetricChoice a b) = foldMap f a <> foldMap f b
  foldMap f (LeftBiasedChoice a b) = foldMap f a <> foldMap f b

collapseChoices :: (Alternative p,  DeterministicParsing p) => ChoiceTree (p a) -> p a
collapseChoices (SymmetricChoice p q) = collapseChoices p <|> collapseChoices q
collapseChoices (LeftBiasedChoice p q) = collapseChoices p <<|> collapseChoices q
collapseChoices (Leaf p) = p

-- | A type of parsers analyzed for their left-recursion class
data SeparatedParser p (g :: (Type -> Type) -> Type) s a =
   -- | a parser that no left-recursive nonterminal depends on
   FrontParser (p g s a)
   -- | a left-recursive parser that may add to the set of parse results every time it's run
   | CycleParser {
        cycleParser  :: p g s a,
        backParser   :: p g s a,
        appendResultsArrow :: ResultAppend p g s a,
        dependencies :: Dependencies g}
   -- | a parser that doesn't start with any 'nonTerminal' so it can run first
   | BackParser {
        backParser :: p g s a}

newtype Union (g :: (Type -> Type) -> Type) = Union{getUnion :: g (Const Bool)}

--instance Rank2.Applicative g => Monoid (Union g) where
--   mempty = Union (Rank2.pure $ Const False)

instance (Rank2.Apply g, Rank2.Distributive g) => Semigroup (Union g) where
   Union g1 <> Union g2 = Union (Rank2.liftA2 union g1 g2)

instance (Rank2.Apply g, Rank2.Distributive g) => Monoid (Union g) where
   mempty = Union (Rank2.cotraverse (Const . getConst) (Const False))
   mappend = (<>)

asLeaf :: Fixed p g s a -> Fixed p g s a
asLeaf p@Parser{} = p'
   where p' = p{choices= Leaf p'}
asLeaf p = p

mapPrimitive :: forall p g s a b. AmbiguityDecidable b => (p g s a -> p g s b) -> Fixed p g s a -> Fixed p g s b
mapPrimitive f p@PositiveDirectParser{} = PositiveDirectParser{complete= f (complete p)}
mapPrimitive f p@DirectParser{} = DirectParser{complete= f (complete p),
                                               direct0= f (direct0 p),
                                               direct1= f (direct1 p)}
mapPrimitive f p@Parser{} = asLeaf Parser{
   complete= f (complete p),
   choices= undefined,
   isAmbiguous= ambiguityWitness @b,
   cyclicDescendants= cyclicDescendants p,
   indirect= f (indirect p),
   direct= f (direct p),
   direct0= f (direct0 p),
   direct1= f (direct1 p)}

general, general' :: (Rank2.Apply g, Alternative (p g s)) => Fixed p g s a -> Fixed p g s a
general p = Parser{
   complete= complete p,
   direct = direct p',
   direct0= direct0 p',
   direct1= direct1 p',
   indirect= indirect p',
   choices= choices p',
   isAmbiguous= case p
                of Parser{isAmbiguous= a} -> a
                   _ -> Nothing,
   cyclicDescendants= cyclicDescendants p'}
   where p' = general' p
general' p@PositiveDirectParser{} = asLeaf Parser{
   complete= complete p,
   direct = complete p,
   direct0= empty,
   direct1= complete p,
   indirect= empty,
   choices= undefined,
   isAmbiguous= Nothing,
   cyclicDescendants= \cd-> ParserFlags False (StaticDependencies $ const (Const False) Rank2.<$> cd)}
general' p@DirectParser{} = asLeaf Parser{
   complete= complete p,
   direct = complete p,
   direct0= direct0 p,
   direct1= direct1 p,
   indirect= empty,
   choices= undefined,
   isAmbiguous= Nothing,
   cyclicDescendants= \cd-> ParserFlags True (StaticDependencies $ const (Const False) Rank2.<$> cd)}
general' p@Parser{} = p

type LeftRecParsing p g s f = (Eq s, LeftReductive s, FactorialMonoid s, Alternative (p g s),
                               TailsParsing (p g s), GrammarConstraint (p g s) g, ParserGrammar (p g s) ~ g,
                               Functor (ResultFunctor (p g s)), s ~ ParserInput (p g s), FallibleResults f,
                               Storable1 (GrammarFunctor (p g s)) (ParserFlags g),
                               Storable1 (GrammarFunctor (p g s)) Bool,
                               AmbiguousAlternative (GrammarFunctor (p g s)))

-- | Parser transformer for left-recursive grammars.
--
-- @
-- 'parseComplete' :: ("Rank2".'Rank2.Apply' g, "Rank2".'Rank2.Traversable' g, 'FactorialMonoid' s) =>
--                  g (LeftRecursive.'Parser' g s) -> s -> g ('Compose' ('ParseResults' s) [])
-- @
instance (Rank2.Apply g, GrammarFunctor (p g s) ~ f s, LeftRecParsing p g s f) => MultiParsing (Fixed p g s) where
   type GrammarConstraint (Fixed p g s) g' = (GrammarConstraint (p g s) g', g ~ g',
                                              Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g)
   type ResultFunctor (Fixed p g s) = ResultFunctor (p g s)
   -- parsePrefix :: (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g, Eq s, FactorialMonoid s) =>
   --                g (Fixed p g s) -> s -> g (Compose (ResultFunctor (p g s)) ((,) s))
   parsePrefix g input
      | Just directs <- Rank2.traverse getDirect g' = parsePrefix directs input
      | otherwise = Rank2.fmap (Compose . parsingResult @(p g s) input) (snd $ head $ parseSeparated g' input)
      where g' = separated g
            getDirect (FrontParser p) = Just p
            getDirect (BackParser p) = Just p
            getDirect CycleParser{} = Nothing
   {-# INLINE parsePrefix #-}
   -- parseComplete :: (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g, Eq s, FactorialMonoid s) =>
   --                  g (Fixed p g s) -> s -> g (ResultFunctor (p g s))
   parseComplete g input
      | Just directs <- Rank2.traverse getDirect g' = parseComplete directs input
      | otherwise = Rank2.fmap ((snd <$>) . parsingResult @(p g s) input)
                    $ snd $ head $ parseAllTails close $ parseSeparated g' input
      where g' = separated g
            getDirect (FrontParser p) = Just p
            getDirect (BackParser p) = Just p
            getDirect CycleParser{} = Nothing
            close :: g (p g s)
            close = Rank2.fmap (<* eof) selfReferring
   {-# INLINE parseComplete #-}

-- | Parser transformer for left-recursive grammars.
instance (Rank2.Apply g, GrammarFunctor (p g s) ~ f s, LeftRecParsing p g s f) => GrammarParsing (Fixed p g s) where
   type ParserGrammar (Fixed p g s) = g
   type GrammarFunctor (Fixed p g s) = GrammarFunctor (p g s)
   parsingResult :: s -> GrammarFunctor (p g s) a -> ResultFunctor (p g s) (s, a)
   parsingResult s = parsingResult @(p g s) s
   nonTerminal :: (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g) =>
                  (g (GrammarFunctor (p g s)) -> GrammarFunctor (p g s) a) -> Fixed p g s a
   nonTerminal f = asLeaf Parser{
      complete= ind,
      direct= empty,
      direct0= empty,
      direct1= empty,
      indirect= ind,
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= reuse1 . f . Rank2.fmap store11 . addSelf}
      where ind = nonTerminal f
            addSelf g = Rank2.liftA2 adjust bits g
            adjust :: forall b. Const (g (Const Bool)) b -> Const (ParserFlags g) b -> Const (ParserFlags g) b
            adjust (Const bit) (Const (ParserFlags n (StaticDependencies d))) =
               Const ParserFlags{
                  nullable= n, 
                  dependsOn= StaticDependencies (Rank2.liftA2 union bit d)}
            adjust _ flags@(Const (ParserFlags _ DynamicDependencies)) = flags
   {-# INLINE nonTerminal #-}
   recursive = general
   chainRecursive = chainWith chainRecursive
   chainLongestRecursive = chainWith chainLongestRecursive

chainWith :: (Rank2.Apply g, GrammarFunctor (p g s) ~ f, f ~ rl s, LeftRecParsing p g s rl)
          => ((f a -> g f -> g f) -> p g s a -> p g s a -> p g s a)
          -> ((f a -> g f -> g f) -> Fixed p g s a -> Fixed p g s a -> Fixed p g s a)
chainWith f assign = chain
  where chain base recurse@Parser{} = asLeaf Parser{
           complete= f assign (complete base) (complete recurse),
           direct= f assign (direct base) (complete recurse),
           direct0= f assign (direct0 base) (complete recurse),
           direct1= f assign (direct1 base) (complete recurse),
           indirect= f assign (indirect base) (complete recurse),
           choices= undefined,
           isAmbiguous= isAmbiguous base <|> isAmbiguous recurse,
           cyclicDescendants= \deps-> let ParserFlags pn pd = cyclicDescendants base deps
                                          ParserFlags qn qd = cyclicDescendants recurse deps
                                          qd' = case qd
                                                of DynamicDependencies -> DynamicDependencies
                                                   StaticDependencies g -> StaticDependencies (clearOwnDep g)
                                      in ParserFlags (pn && qn) (depUnion pd qd')}
        chain base recurse = recurse <|> base
        clearOwnDep = Rank2.fmap reuse11 . assign (store11 $ Const False) . Rank2.fmap store11

bits :: forall (g :: (Type -> Type) -> Type). (Rank2.Distributive g, Rank2.Traversable g) => g (Const (g (Const Bool)))
bits = start `seq` Rank2.fmap oneBit start
   where start = evalState (Rank2.traverse next (Rank2.distributeJoin Nothing)) 0
         oneBit :: Const Int a -> Const (g (Const Bool)) a
         next :: f a -> State Int (Const Int a)
         oneBit (Const i) = Const (Rank2.fmap (Const . (i ==) . getConst) start)
         next _ = do {i <- State.get; let {i' = succ i}; seq i' (State.put i'); return (Const i)}

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
      indirect= fmap f (indirect p),
      choices= fmap f <$> choices p,
      isAmbiguous= Nothing}
   {-# INLINABLE fmap #-}

instance (Rank2.Apply g, Alternative (p g s)) => Applicative (Fixed p g s) where
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
   p <*> q@Parser{} = asLeaf Parser{
      complete= complete p' <*> complete q,
      direct= direct0 p' <*> direct q <|> direct1 p' <*> complete q,
      direct0= direct0 p' <*> direct0 q,
      direct1= direct0 p' <*> direct1 q <|> direct1 p' <*> complete q,
      indirect= direct0 p' <*> indirect q <|> indirect p' <*> complete q,
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= \deps-> let
           pcd@(ParserFlags pn pd) = cyclicDescendants p' deps
           ParserFlags qn qd = cyclicDescendants q deps
        in if pn
           then ParserFlags qn (depUnion pd qd)
           else pcd}
      where p'@Parser{} = general' p
   p <*> q = asLeaf Parser{
      complete= complete p' <*> complete q',
      direct= direct p' <*> complete q',
      direct0= direct0 p' <*> direct0 q',
      direct1= direct0 p' <*> direct1 q' <|> direct1 p' <*> complete q',
      indirect= indirect p' <*> complete q',
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= \deps-> let
           pcd@(ParserFlags pn pd) = cyclicDescendants p' deps
           ParserFlags qn qd = cyclicDescendants q' deps
        in if pn
           then ParserFlags qn (depUnion pd qd)
           else pcd}
      where p'@Parser{} = general' p
            q'@Parser{} = general' q
   {-# INLINABLE pure #-}
   {-# INLINABLE (<*>) #-}

instance (Rank2.Apply g, Alternative (p g s)) => Alternative (Fixed p g s) where
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
                    choices= choices p' `SymmetricChoice` choices q',
                    isAmbiguous= Nothing,
                    cyclicDescendants= \deps-> let
                         ParserFlags pn pd = cyclicDescendants p' deps
                         ParserFlags qn qd = cyclicDescendants q' deps
                      in ParserFlags (pn || qn) (depUnion pd qd)}
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
   many p@Parser{} = asLeaf Parser{
      complete= mcp,
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= (:) <$> indirect p <*> mcp,
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}
      where d0 = pure [] <|> (:[]) <$> direct0 p
            d1 = (:) <$> direct1 p <*> mcp
            mcp = many (complete p)
   some (PositiveDirectParser p) = PositiveDirectParser{complete= some p}
   some p@DirectParser{} = DirectParser{
      complete= some (complete p),
      direct0= (:[]) <$> direct0 p,
      direct1= (:) <$> direct1 p <*> many (complete p)}
   some p@Parser{} = asLeaf Parser{
      complete= some (complete p),
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= (:) <$> indirect p <*> many (complete p),
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= cyclicDescendants p}
      where d0 = (:[]) <$> direct0 p
            d1= (:) <$> direct1 p <*> many (complete p)
   {-# INLINABLE (<|>) #-}
   {-# INLINABLE many #-}
   {-# INLINABLE some #-}

instance Filterable (p g s) => Filterable (Fixed p g s) where
   mapMaybe f (PositiveDirectParser p) = PositiveDirectParser (mapMaybe f p)
   mapMaybe f p@DirectParser{} = DirectParser{
      complete= mapMaybe f (complete p),
      direct0= mapMaybe f (direct0 p),
      direct1= mapMaybe f (direct1 p)}
   mapMaybe f p@Parser{} = p{
      complete= mapMaybe f (complete p),
      direct= mapMaybe f (direct p),
      direct0= mapMaybe f (direct0 p),
      direct1= mapMaybe f (direct1 p),
      indirect= mapMaybe f (indirect p),
      choices= mapMaybe f <$> choices p,
      isAmbiguous= Nothing}
   {-# INLINABLE mapMaybe #-}

complement :: Const Bool x -> Const Bool x
complement (Const a) = Const (not a)

intersection :: Const Bool x -> Const Bool x -> Const Bool x
intersection (Const True) x = x
intersection (Const False) _ = Const False

union :: Const Bool x -> Const Bool x -> Const Bool x
union (Const False) x = x
union (Const True) _ = Const True

depUnion :: Rank2.Apply g => Dependencies g -> Dependencies g -> Dependencies g
depUnion (StaticDependencies d1) (StaticDependencies d2) = StaticDependencies (Rank2.liftA2 union d1 d2)
depUnion _ _ = DynamicDependencies

instance (Rank2.Apply g, Alternative (p g s), Monad (p g s)) => Monad (Fixed p g s) where
   return = pure
   (>>) = (*>)
   PositiveDirectParser p >>= cont = PositiveDirectParser (p >>= complete . cont)
   p@DirectParser{} >>= cont = asLeaf Parser{
      complete= complete p >>= complete . cont,
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= direct0 p >>= indirect . general' . cont,
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= const (ParserFlags True DynamicDependencies)}
      where d0 = direct0 p >>= direct0 . general' . cont
            d1 = (direct0 p >>= direct1 . general' . cont) <|> (direct1 p >>= complete . cont)
   p >>= cont = asLeaf Parser{
      complete= complete p >>= complete . cont,
      direct= d0 <|> d1,
      direct0= d0,
      direct1= d1,
      indirect= (indirect p >>= complete . cont) <|> (direct0 p >>= indirect . general' . cont),
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= \cd->
         let pcd@(ParserFlags pn _) = cyclicDescendants p' cd
         in if pn
            then ParserFlags True DynamicDependencies
            else pcd}
      where d0 = direct0 p >>= direct0 . general' . cont
            d1 = (direct0 p >>= direct1 . general' . cont) <|> (direct1 p >>= complete . cont)
            p'@Parser{} = general' p

#if MIN_VERSION_base(4,13,0)
instance (Rank2.Apply g, Alternative (p g s), MonadFail (p g s)) => MonadFail (Fixed p g s) where
#endif
   fail msg = PositiveDirectParser{complete= fail msg}

instance (Rank2.Apply g, MonadPlus (p g s)) => MonadPlus (Fixed p g s) where
   mzero = empty
   mplus = (<|>)

instance (Rank2.Apply g, Alternative (p g s), Semigroup x) => Semigroup (Fixed p g s x) where
   (<>) = liftA2 (<>)

instance (Rank2.Apply g, Alternative (p g s), Monoid x) => Monoid (Fixed p g s x) where
   mempty = pure mempty
   mappend = (<>)

primitive :: p g s a -> p g s a -> p g s a -> Fixed p g s a
primitive d0 d1 d = DirectParser{complete= d,
                                 direct0= d0,
                                 direct1= d1}
{-# INLINE primitive #-}

-- | Lifts a primitive positive parser (/i.e./, one that always consumes some input) into a left-recursive one
liftPositive :: p g s a -> Fixed p g s a
liftPositive p = PositiveDirectParser{complete= p}
{-# INLINE liftPositive #-}

-- | Lifts a primitive pure parser (/i.e./, one that consumes no input) into a left-recursive one
liftPure :: Alternative (p g s) => p g s a -> Fixed p g s a
liftPure p = DirectParser{complete= p,
                          direct0= p,
                          direct1= empty}
{-# INLINE liftPure #-}

instance (Rank2.Apply g, Parsing (p g s), InputParsing (Fixed p g s)) => Parsing (Fixed p g s) where
   eof = primitive eof empty eof
   try (PositiveDirectParser p) = PositiveDirectParser (try p)
   try p@DirectParser{} = DirectParser{
      complete= try (complete p),
      direct0= try (direct0 p),
      direct1= try (direct1 p)}
   try p@Parser{} = asLeaf p{
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
   p@Parser{} <?> msg = asLeaf p{
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
   notFollowedBy p@Parser{} = asLeaf Parser{
      complete= notFollowedBy (complete p),
      direct= notFollowedBy (direct p),
      direct0= notFollowedBy (direct p),
      direct1= empty,
      indirect= notFollowedBy (indirect p),
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}
   unexpected msg = liftPositive (unexpected msg)

instance (Rank2.Apply g, InputParsing (Fixed p g s), DeterministicParsing (p g s)) =>
         DeterministicParsing (Fixed p g s) where
   p@DirectParser{} <<|> q@PositiveDirectParser{} = DirectParser{
      complete= complete p <<|> complete q,
      direct0 = direct0 p,
      direct1= direct1 p <<|> complete q}
   p@DirectParser{} <<|> q@DirectParser{} = DirectParser{
      complete= complete p <<|> complete q,
      direct0 = direct0 p <<|> direct0 q,
      direct1= direct1 p <<|> direct1 q}
   p <<|> q = Parser{complete= complete p' <<|> complete q',
                     direct= direct p' <<|> notFollowedBy (void $ complete p') *> direct q',
                     direct0= direct0 p' <<|> notFollowedBy (void $ complete p') *> direct0 q',
                     direct1= direct1 p' <<|> notFollowedBy (void $ complete p') *> direct1 q',
                     indirect= indirect p' <<|> notFollowedBy (void $ complete p') *> indirect q',
                     choices= choices p' `LeftBiasedChoice` choices q',
                     isAmbiguous= Nothing,
                     cyclicDescendants= \deps-> let
                           ParserFlags pn pd = cyclicDescendants p' deps
                           ParserFlags qn qd = cyclicDescendants q' deps
                        in ParserFlags (pn || qn) (depUnion pd qd)}
      where p'@Parser{} = general p
            q'@Parser{} = general q
   takeSome p = (:) <$> p <*> takeMany p
   takeMany (PositiveDirectParser p) = DirectParser{
      complete = takeMany p,
      direct0= [] <$ notFollowedBy (void p),
      direct1= takeSome p}
   takeMany p@DirectParser{} = DirectParser{
      complete = takeMany (complete p),
      direct0= (:[]) <$> direct0 p <<|> [] <$ notFollowedBy (void $ complete p),
      direct1= (:) <$> direct1 p <*> takeMany (complete p)}
   takeMany p@Parser{} = asLeaf Parser{
      complete= mcp,
      direct= d1 <<|> d0,
      direct0= d0,
      direct1= d1,
      indirect= (:) <$> indirect p <*> mcp,
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}
      where d0 = (:[]) <$> direct0 p <<|> [] <$ notFollowedBy (void $ direct p)
            d1 = (:) <$> direct1 p <*> mcp
            mcp = takeMany (complete p)
   skipAll (PositiveDirectParser p) = DirectParser{
      complete = skipAll p,
      direct0= () <$ notFollowedBy (void p),
      direct1= p *> skipAll p}
   skipAll p@DirectParser{} = DirectParser{
      complete = skipAll (complete p),
      direct0= void (direct0 p) <<|> notFollowedBy (void $ complete p),
      direct1= direct1 p *> skipAll (complete p)}
   skipAll p@Parser{} = asLeaf Parser{
      complete= mcp,
      direct= d1 <<|> d0,
      direct0= d0,
      direct1= d1,
      indirect= indirect p *> mcp,
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}
      where d0 = () <$ direct0 p <<|> notFollowedBy (void $ direct p)
            d1 = direct1 p *> mcp
            mcp = skipAll (complete p)

instance (Rank2.Apply g, CommittedParsing (p g s), CommittedResults (p g s) ~ ParseResults s) =>
         CommittedParsing (Fixed p g s) where
   type CommittedResults (Fixed p g s) = ParseResults s
   commit (PositiveDirectParser p) = PositiveDirectParser (commit p)
   commit p@DirectParser{} = DirectParser{
      complete = commit (complete p),
      direct0= commit (direct0 p),
      direct1= commit (direct1 p)}
   commit p@Parser{} = asLeaf Parser{
      complete= commit (complete p),
      direct= commit (direct p),
      direct0= commit (direct0 p),
      direct1= commit (direct1 p),
      indirect= commit (indirect p),
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= cyclicDescendants p}
   admit :: Fixed p g s (CommittedResults (Fixed p g s) a) -> Fixed p g s a
   admit (PositiveDirectParser p) = PositiveDirectParser (admit p)
   admit p@DirectParser{} = DirectParser{
      complete = admit (complete p),
      direct0= admit (direct0 p),
      direct1= admit (direct1 p)}
   admit p@Parser{} = asLeaf Parser{
      complete= admit (complete p),
      direct= admit (direct p),
      direct0= admit (direct0 p),
      direct1= admit (direct1 p),
      indirect= admit (indirect p),
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= cyclicDescendants p}

instance (Rank2.Apply g, LookAheadParsing (p g s), InputParsing (Fixed p g s)) => LookAheadParsing (Fixed p g s) where
   lookAhead p@PositiveDirectParser{} = DirectParser{
      complete= lookAhead (complete p),
      direct0= lookAhead (complete p),
      direct1= empty}
   lookAhead p@DirectParser{} = DirectParser{
      complete= lookAhead (complete p),
      direct0= lookAhead (complete p),
      direct1= empty}
   lookAhead p@Parser{} = asLeaf Parser{
      complete= lookAhead (complete p),
      direct= lookAhead (direct p),
      direct0= lookAhead (direct p),
      direct1= empty,
      isAmbiguous= isAmbiguous p,
      indirect= lookAhead (indirect p),
      choices= undefined,
      cyclicDescendants= \deps-> (cyclicDescendants p deps){nullable= True}}

instance (Rank2.Apply g, LeftReductive s, FactorialMonoid s, InputParsing (p g s), ParserInput (p g s) ~ s) =>
         InputParsing (Fixed p g s) where
   type ParserInput (Fixed p g s) = s
   getInput = primitive getInput empty getInput
   anyToken = liftPositive anyToken
   satisfy predicate = liftPositive (satisfy predicate)
   notSatisfy predicate = primitive (notSatisfy predicate) empty (notSatisfy predicate)
   scan s0 f = primitive (mempty <$ notSatisfy test) (lookAhead (satisfy test) *> p) p
      where p = scan s0 f
            test = isJust . f s0
   string s
      | null s = primitive (string s) empty (string s)
      | otherwise = liftPositive (string s)
   take 0 = mempty
   take n = liftPositive (take n)
   takeWhile predicate = primitive (mempty <$ notSatisfy predicate)
                                               (takeWhile1 predicate) (takeWhile predicate)
   takeWhile1 predicate = liftPositive (takeWhile1 predicate)

   {-# INLINABLE string #-}

instance (Rank2.Apply g, LeftReductive s, FactorialMonoid s, Show s,
          TraceableParsing (p g s), ParserInput (p g s) ~ s) =>
         TraceableParsing (Fixed p g s) where
   traceInput description p@PositiveDirectParser{} = p{
      complete= traceInput (\s-> "direct+ " <> description s) (complete p)}
   traceInput description p@DirectParser{} = p{
      complete= traceInput (\s-> "direct " <> description s) (complete p),
      direct0= traceInput (\s-> "direct0 " <> description s) (direct0 p),
      direct1= traceInput (\s-> "direct1 " <> description s) (direct1 p)}
   traceInput description p@Parser{} = asLeaf p{
      complete= traceBy "complete" (complete p),
      direct= traceBy "direct" (direct p),
      direct0= traceBy "direct0" (direct0 p),
      direct1= traceBy "direct1" (direct1 p),
      indirect= traceBy "indirect" (indirect p)}
      where traceBy mode = traceInput (\s-> "(" <> mode <> ") " <> description s)

instance (Rank2.Apply g, LeftReductive s, FactorialMonoid s,
          ConsumedInputParsing (p g s), ParserInput (p g s) ~ s) => ConsumedInputParsing (Fixed p g s) where
   match (PositiveDirectParser p) = PositiveDirectParser (match p)
   match p@DirectParser{} = DirectParser{
      complete= match (complete p),
      direct0 = match (direct0 p),
      direct1 = match (direct1 p)}
   match p@Parser{} = asLeaf Parser{
      complete= match (complete p),
      direct =  match (direct p),
      direct0 = match (direct0 p),
      direct1 = match (direct1 p),
      indirect= match (indirect p),
      choices= undefined,
      isAmbiguous= Nothing,
      cyclicDescendants= cyclicDescendants p}

instance (Rank2.Apply g, Show s, TextualMonoid s, InputCharParsing (p g s), ParserInput (p g s) ~ s) =>
         InputCharParsing (Fixed p g s) where
   satisfyCharInput predicate = liftPositive (satisfyCharInput predicate)
   notSatisfyChar predicate = primitive (notSatisfyChar predicate) empty (notSatisfyChar predicate)
   scanChars s0 f = primitive (mempty <$ notSatisfyChar test) (lookAhead (Char.satisfy test) *> p) p
      where p = scanChars s0 f
            test = isJust . f s0
   takeCharsWhile predicate = primitive (mempty <$ notSatisfyChar predicate)
                                        (takeCharsWhile1 predicate) (takeCharsWhile predicate)
   takeCharsWhile1 predicate = liftPositive (takeCharsWhile1 predicate)

instance (Rank2.Apply g, CharParsing (p g s), InputCharParsing (Fixed p g s), TextualMonoid s,
          s ~ ParserInput (Fixed p g s), Show s) => CharParsing (Fixed p g s) where
   satisfy predicate = liftPositive (Char.satisfy predicate)
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (AmbiguousParsing (p g s), Rank2.Apply g) => AmbiguousParsing (Fixed p g s) where
   ambiguous (PositiveDirectParser p) = PositiveDirectParser (ambiguous p)
   ambiguous p@DirectParser{} = DirectParser{complete= ambiguous (complete p),
                                             direct0=  ambiguous (direct0 p),
                                             direct1=  ambiguous (direct1 p)}
   ambiguous p@Parser{} = asLeaf Parser{
      complete= ambiguous (complete p),
      direct=   ambiguous (direct p),
      direct0=  ambiguous (direct0 p),
      direct1=  ambiguous (direct1 p),
      indirect= ambiguous (indirect p),
      choices= undefined,
      isAmbiguous= Just (AmbiguityWitness Refl),
      cyclicDescendants= cyclicDescendants p}
   {-# INLINABLE ambiguous #-}

-- | Turns a context-free parser into a backtracking PEG parser that consumes the longest possible prefix of the list
-- of input tails, opposite of 'peg'
longest :: Fixed Memoizing.Parser g s a -> Fixed Backtrack.Parser g [(s, g (ResultList g s))] a
longest (PositiveDirectParser p) = PositiveDirectParser (Memoizing.longest p)
longest p@DirectParser{} = DirectParser{complete= Memoizing.longest (complete p),
                                        direct0=  Memoizing.longest (direct0 p),
                                        direct1=  Memoizing.longest (direct1 p)}
longest p@Parser{} = asLeaf Parser{
   complete= Memoizing.longest (complete p),
   direct=  Memoizing.longest (direct p),
   direct0=  Memoizing.longest (direct0 p),
   direct1=  Memoizing.longest (direct1 p),
   indirect=  Memoizing.longest (indirect p),
   choices= undefined,
   isAmbiguous= Nothing,
   cyclicDescendants= cyclicDescendants p}

-- | Turns a backtracking PEG parser of the list of input tails into a context-free parser, opposite of 'longest'
peg :: Ord s => Fixed Backtrack.Parser g [(s, g (ResultList g s))] a -> Fixed Memoizing.Parser g s a
peg (PositiveDirectParser p) = PositiveDirectParser (Memoizing.peg p)
peg p@DirectParser{} = DirectParser{complete= Memoizing.peg (complete p),
                                        direct0=  Memoizing.peg (direct0 p),
                                        direct1=  Memoizing.peg (direct1 p)}
peg p@Parser{} = asLeaf Parser{
   complete= Memoizing.peg (complete p),
   direct=  Memoizing.peg (direct p),
   direct0=  Memoizing.peg (direct0 p),
   direct1=  Memoizing.peg (direct1 p),
   indirect=  Memoizing.peg (indirect p),
   choices= undefined,
   isAmbiguous= Nothing,
   cyclicDescendants= cyclicDescendants p}

-- | Turns a backtracking PEG parser into a context-free parser
terminalPEG :: (Monoid s, Ord s) => Fixed Backtrack.Parser g s a -> Fixed Memoizing.Parser g s a
terminalPEG (PositiveDirectParser p) = PositiveDirectParser (Memoizing.terminalPEG p)
terminalPEG p@DirectParser{} = DirectParser{complete= Memoizing.terminalPEG (complete p),
                                            direct0=  Memoizing.terminalPEG (direct0 p),
                                            direct1=  Memoizing.terminalPEG (direct1 p)}
terminalPEG p@Parser{} = asLeaf Parser{
   complete= Memoizing.terminalPEG (complete p),
   direct=  Memoizing.terminalPEG (direct p),
   direct0=  Memoizing.terminalPEG (direct0 p),
   direct1=  Memoizing.terminalPEG (direct1 p),
   indirect=  Memoizing.terminalPEG (indirect p),
   choices= undefined,
   isAmbiguous= Nothing,
   cyclicDescendants= cyclicDescendants p}

-- | Automatically apply 'chainRecursive' and 'chainLongestRecursive' to left-recursive grammar productions where
-- possible.
autochain :: forall p g s f rl (cb :: Type -> Type).
             (cb ~ Const (g (Const Bool)), f ~ GrammarFunctor (p g s), f ~ rl s,
              LeftRecParsing p g s rl, DeterministicParsing (p g s),
              Rank2.Apply g, Rank2.Traversable g, Rank2.Distributive g, Rank2.Logistic g)
          => g (Fixed p g s) -> g (Fixed p g s)
autochain g = Rank2.liftA4 optimize Rank2.getters Rank2.setters candidates g
   where candidates :: g (Const Bool)
         optimize :: forall a. (Compose ((->) (g cb)) cb a)
                  -> (Rank2.Arrow (f Rank2.~> f) (Const (g f -> g f)) a)
                  -> Const Bool a
                  -> Fixed p g s a
                  -> Fixed p g s a
         optimize getter setter (Const True) p@Parser{choices= cs} =
            optimizeChoice (getCompose getter) (getConst . Rank2.apply setter . Rank2.Arrow . const) p cs
         optimize _ _ _ p = p
         optimizeChoice :: (g cb -> cb a)
                        -> (f a -> g f -> g f)
                        -- > (forall f. (f a -> f a) -> g f -> g f)
                        -- > (forall f. Rank2.Arrow f f a -> Const (g f -> g f) a)
                        -> Fixed p g s a
                        -> ChoiceTree (Fixed p g s a)
                        -> Fixed p g s a
         splitSymmetric :: (g cb -> cb a) -> ChoiceTree (Fixed p g s a) -> ([Fixed p g s a], [Fixed p g s a])
         isLeftRecursive :: (g cb -> cb a) -> ChoiceTree (Fixed p g s a) -> Bool
         leftRecursiveParser :: (g cb -> cb a) -> Fixed p g s a -> Bool
         optimizeChoice _ _ fallback Leaf{} = fallback
         optimizeChoice get set fallback (LeftBiasedChoice p q)
            | isLeftRecursive get q = fallback
            | not (isLeftRecursive get p) = fallback
            | LeftBiasedChoice p1 p2 <- p, not (isLeftRecursive get p2)
            = optimizeChoice get set fallback $ LeftBiasedChoice p1 (LeftBiasedChoice p2 q)
            | otherwise = chainLongestRecursive set (collapseChoices q) (collapseChoices p)
         optimizeChoice get set fallback c@SymmetricChoice{}
            | null base = fallback
            | null recursives = fallback
            | otherwise = chainRecursive set (foldr1 (<|>) base) (foldr1 (<|>) recursives)
            where (base, recursives) = splitSymmetric get c
         splitSymmetric get (SymmetricChoice p q) = splitSymmetric get p <> splitSymmetric get q
         splitSymmetric get c
            | isLeftRecursive get c = ([], [collapseChoices c])
            | otherwise = ([collapseChoices c], [])
         isLeftRecursive get = leftRecursiveParser get . collapseChoices
         leftRecursiveParser get Parser{cyclicDescendants= cds} =
            getAny $ Rank2.foldMap (Any . getConst) $ Rank2.liftA2 intersection (getConst $ get bits) (deps bits)
            where deps :: g cb -> g (Const Bool)
                  deps = getDependencies . dependsOn . cds
                         . Rank2.fmap (Const . ParserFlags False . StaticDependencies . getConst)
         leftRecursiveParser _ _ = False
         candidates = Rank2.liftA2 intersection (cyclicDependencies g) (complement Rank2.<$> cyclicDependencies g')
         g' = Rank2.liftA2 noDirectLeftRecursion bits g
         noDirectLeftRecursion (Const bit) p@Parser{cyclicDescendants= cd} = p{cyclicDescendants= excludeSelf . cd}
            where excludeSelf (ParserFlags n DynamicDependencies) = ParserFlags n DynamicDependencies
                  excludeSelf (ParserFlags n (StaticDependencies deps)) =
                     ParserFlags n $ StaticDependencies $ Rank2.liftA2 intersection (complement Rank2.<$> bit) deps
         noDirectLeftRecursion _ p = p

parseRecursive :: forall p g s rl. (Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g,
                                    Eq s, FactorialMonoid s, LeftReductive s, Alternative (p g s),
                                    TailsParsing (p g s), GrammarConstraint (p g s) g,
                                    s ~ ParserInput (p g s), GrammarFunctor (p g s) ~ rl s, FallibleResults rl,
                                    AmbiguousAlternative (GrammarFunctor (p g s))) =>
                  g (Fixed p g s) -> s -> [(s, g (GrammarFunctor (p g s)))]
parseRecursive = parseSeparated . separated
{-# INLINE parseRecursive #-}

-- | Analyze the grammar's production interdependencies and produce a 'SeparatedParser' from each production's parser.
separated :: forall p g s. (Alternative (p g s), Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g,
                            AmbiguousAlternative (GrammarFunctor (p g s))) =>
             g (Fixed p g s) -> g (SeparatedParser p g s)
separated g = Rank2.liftA4 reseparate circulars cycleFollowers descendants g
   where descendants :: g (Const (Dependencies g))
         cycleFollowers, circulars :: g (Const Bool)
         appendResults :: forall a. Maybe (AmbiguityWitness a)
                       -> GrammarFunctor (p g s) a -> GrammarFunctor (p g s) a -> GrammarFunctor (p g s) a
         leftRecursiveDeps :: forall a. Const Bool a -> Const (Dependencies g) a -> Const (g (Const Bool)) a
         reseparate :: forall a. Const Bool a -> Const Bool a -> Const (Dependencies g) a -> Fixed p g s a
                    -> SeparatedParser p g s a
         reseparate (Const circular) (Const follower) (Const d@(StaticDependencies deps)) p
            | circular || leader && follower =
              CycleParser (indirect p) (direct p) (Rank2.Arrow (Rank2.Arrow . appendResults (isAmbiguous p))) d
            | follower = BackParser (complete p)
            | otherwise = FrontParser (complete p)
            where leader = getAny (Rank2.foldMap (Any . getConst) $ Rank2.liftA2 intersection circulars deps)
         reseparate _ _ (Const d@DynamicDependencies) p =
              CycleParser (indirect p) (direct p) (Rank2.Arrow (Rank2.Arrow . appendResults (isAmbiguous p))) d
         appendResults (Just (AmbiguityWitness Refl)) = ambiguousOr
         appendResults Nothing = (<|>)
         descendants = transitiveDescendants g
         circulars = Rank2.liftA2 leftRecursive bits descendants
         cycleFollowers = getUnion (Rank2.foldMap (Union . getConst) $
                                    Rank2.liftA2 leftRecursiveDeps circulars descendants)
         leftRecursiveDeps (Const True) (Const (StaticDependencies deps)) = Const deps
         leftRecursiveDeps (Const False) (Const (StaticDependencies deps)) =
            Const (Rank2.fmap (const $ Const False) deps)
         leftRecursiveDeps _ (Const DynamicDependencies) = Const (Rank2.fmap (const $ Const True) g)
{-# INLINABLE separated #-}

getDependencies :: Rank2.Distributive g => Dependencies g -> g (Const Bool)
getDependencies (StaticDependencies deps) = deps
getDependencies DynamicDependencies = Rank2.cotraverse (const $ Const True) Nothing

cyclicDependencies :: (Alternative (p g s), Rank2.Apply g, Rank2.Distributive g, Rank2.Traversable g)
                   => g (Fixed p g s) -> g (Const Bool)
cyclicDependencies = Rank2.liftA2 leftRecursive bits . transitiveDescendants

leftRecursive :: forall g a. (Rank2.Apply g, Rank2.Foldable g)
              => Const (g (Const Bool)) a -> Const (Dependencies g) a -> Const Bool a
leftRecursive (Const bit) (Const (StaticDependencies deps)) =
   Const (getAny $ Rank2.foldMap (Any . getConst) $ Rank2.liftA2 intersection bit deps)
leftRecursive _ (Const DynamicDependencies) = Const True

transitiveDescendants :: (Alternative (p g s), Rank2.Apply g, Rank2.Traversable g)
                      => g (Fixed p g s) -> g (Const (Dependencies g))
transitiveDescendants =
   Rank2.fmap (Const . dependsOn . getConst) . fixDescendants . Rank2.fmap (Const . cyclicDescendants . general)

fixDescendants :: forall g. (Rank2.Apply g, Rank2.Traversable g)
               => g (Const (g (Const (ParserFlags g)) -> (ParserFlags g))) -> g (Const (ParserFlags g))
fixDescendants gf = go initial
   where go :: g (Const (ParserFlags g)) -> g (Const (ParserFlags g))
         go cd
            | getAll (Rank2.foldMap (All . getConst) $ Rank2.liftA2 agree cd cd') = cd
            | otherwise = go cd'
            where cd' = Rank2.liftA2 flagUnion cd (Rank2.fmap (\(Const f)-> Const (f cd)) gf)
         agree (Const (ParserFlags _xn (StaticDependencies xd))) (Const (ParserFlags _yn (StaticDependencies yd))) =
            Const (getAll (Rank2.foldMap (All . getConst) (Rank2.liftA2 agree' xd yd)))
         agree (Const (ParserFlags _xn DynamicDependencies)) (Const (ParserFlags _yn DynamicDependencies)) = Const True
         agree _ _ = Const False
         agree' (Const x) (Const y) = Const (x == y)
         flagUnion (Const ParserFlags{dependsOn= old}) (Const (ParserFlags n new)) = 
            Const (ParserFlags n $ depUnion old new)
         initial = Rank2.liftA2 (\_ (Const n)-> Const (ParserFlags n deps)) gf nullabilities
         deps = StaticDependencies (const (Const False) Rank2.<$> gf)
         nullabilities = fixNullabilities gf
{-# INLINABLE fixDescendants #-}

fixNullabilities :: forall g. (Rank2.Apply g, Rank2.Traversable g)
                    => g (Const (g (Const (ParserFlags g)) -> (ParserFlags g))) -> g (Const Bool)
fixNullabilities gf = Const . nullable . getConst Rank2.<$> go initial
   where go :: g (Const (ParserFlags g)) -> g (Const (ParserFlags g))
         go cd
            | getAll (Rank2.foldMap (All . getConst) $ Rank2.liftA2 agree cd cd') = cd
            | otherwise = go cd'
            where cd' = Rank2.fmap (\(Const f)-> Const (f cd)) gf
         agree (Const flags1) (Const flags2) = Const (nullable flags1 == nullable flags2)
         initial = const (Const (ParserFlags True (StaticDependencies $ const (Const False) Rank2.<$> gf))) Rank2.<$> gf
{-# INLINABLE fixNullabilities #-}

-- | Parse the given input using a context-free grammar 'separated' into left-recursive and other productions.
parseSeparated :: forall p g rl s. (Rank2.Apply g, Rank2.Foldable g, Eq s, FactorialMonoid s, LeftReductive s,
                                    TailsParsing (p g s), GrammarConstraint (p g s) g,
                                    GrammarFunctor (p g s) ~ rl s, FallibleResults rl,
                                    s ~ ParserInput (p g s)) =>
                  g (SeparatedParser p g s) -> s -> [(s, g (GrammarFunctor (p g s)))]
parseSeparated parsers input = foldr parseTail [] (Factorial.tails input)
   where parseTail s parsedTail = parsed
            where parsed = (s,d''):parsedTail
                  d      = Rank2.fmap (($ (s,d):parsedTail) . parseTails) directs
                  d'     = fixRecursive s parsedTail d
                  d''    = Rank2.liftA2 f parsers d'
                  f :: forall a. SeparatedParser p g s a -> GrammarFunctor (p g s) a -> GrammarFunctor (p g s) a
                  f (FrontParser p) _ = parseTails p ((s,d''):parsedTail)
                  f _ result = result
         fixRecursive :: s -> [(s, g (GrammarFunctor (p g s)))]
                      -> g (GrammarFunctor (p g s)) -> g (GrammarFunctor (p g s))
         whileAnyContinues :: (g (GrammarFunctor (p g s)) -> g (GrammarFunctor (p g s)))
                           -> (g (GrammarFunctor (p g s)) -> g (GrammarFunctor (p g s)))
                           -> g (GrammarFunctor (p g s)) -> g (GrammarFunctor (p g s)) -> g (GrammarFunctor (p g s))
         recurseTotal :: s -> g (GrammarFunctor (p g s) Rank2.~> GrammarFunctor (p g s))
                      -> [(s, g (GrammarFunctor (p g s)))]
                      -> g (GrammarFunctor (p g s))
                      -> g (GrammarFunctor (p g s))
         recurseMarginal :: s -> [(s, g (GrammarFunctor (p g s)))]
                      -> g (GrammarFunctor (p g s))
                      -> g (GrammarFunctor (p g s))
         maybeDependencies :: g (Const (Maybe (Dependencies g)))
         maybeDependency :: SeparatedParser p g s r -> Const (Maybe (Dependencies g)) r
         appends :: g (ResultAppend p g s)
         parserAppend :: SeparatedParser p g s r -> ResultAppend p g s r

         directs = Rank2.fmap backParser parsers
         indirects = Rank2.fmap (\p-> case p of {CycleParser{}-> cycleParser p; _ -> empty}) parsers
         appends = Rank2.fmap parserAppend parsers
         parserAppend p@CycleParser{} = appendResultsArrow p
         parserAppend _ = Rank2.Arrow (Rank2.Arrow . const)
         maybeDependencies = Rank2.fmap maybeDependency parsers
         maybeDependency p@CycleParser{} = Const (Just $ dependencies p)
         maybeDependency _ = Const Nothing

         -- Fix the recursive knot on the head of the input, given its already-fixed tail and the initial record of
         -- directly parsed results.
         fixRecursive s parsedTail initial =
            whileAnyContinues (recurseTotal s (appends Rank2.<*> initial) parsedTail)
                              (recurseMarginal s parsedTail)
                              initial initial

         -- Loop accumulating the total parsing results from marginal results as long as there is any new marginal
         -- result to expand a total one or a new failure expactation to augment an existing failure.
         whileAnyContinues ft fm total marginal =
            Rank2.liftA3 choiceWhile maybeDependencies total (whileAnyContinues ft fm (ft total) (fm marginal))
            where choiceWhile :: Const (Maybe (Dependencies g)) x
                              -> GrammarFunctor (p g s) x -> GrammarFunctor (p g s) x
                              -> GrammarFunctor (p g s) x
                  choiceWhile (Const Nothing) t _ = t
                  choiceWhile (Const (Just (StaticDependencies deps))) t t'
                     | getAny (Rank2.foldMap (Any . getConst) (Rank2.liftA2 combine deps marginal)) = t'
                     | hasSuccess t = t
                     | otherwise =
                        failWith (failureOf $
                                  if getAny (Rank2.foldMap (Any . getConst) $
                                             Rank2.liftA2 (combineFailures $ failureOf t) deps marginal)
                                  then t' else t)
                     where combine :: Const Bool x -> GrammarFunctor (p g s) x -> Const Bool x
                           combineFailures :: ParseFailure Pos s -> Const Bool x -> GrammarFunctor (p g s) x
                                           -> Const Bool x
                           combine (Const False) _ = Const False
                           combine (Const True) results = Const (hasSuccess results)
                           combineFailures _ (Const False) _ = Const False
                           combineFailures (ParseFailure pos expected erroneous) (Const True) rl =
                              Const (pos < pos'
                                     || pos == pos' && (any (`notElem` expected) expected'
                                                        || any (`notElem` erroneous) erroneous'))
                              where ParseFailure pos' expected' erroneous' = failureOf rl
                  choiceWhile (Const (Just DynamicDependencies)) t t'
                     | getAny (Rank2.foldMap (Any . hasSuccess) marginal) = t'
                     | hasSuccess t = t
                     | ParseFailure _ [] [] <- failureOf t = t'
                     | otherwise = t

         -- Adds another round of indirect parsing results to the total results accumulated so far.
         recurseTotal s initialAppends parsedTail total = Rank2.liftA2 reparse initialAppends indirects
            where reparse :: (GrammarFunctor (p g s) Rank2.~> GrammarFunctor (p g s)) a -> p g s a
                          -> GrammarFunctor (p g s) a
                  reparse append p = Rank2.apply append (parseTails p $ (s, total) : parsedTail)
         -- Calculates the next round of indirect parsing results from the previous marginal round.
         recurseMarginal s parsedTail marginal =
            flip parseTails ((s, marginal) : parsedTail) Rank2.<$> indirects
{-# NOINLINE parseSeparated #-}
