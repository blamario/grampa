{-# LANGUAGE ConstrainedClassMethods, FlexibleContexts, FlexibleInstances, GADTs,
             RankNTypes, StandaloneDeriving, TypeOperators, UndecidableInstances #-}

module Text.Grampa.Internal (BinTree(..), ResultList(..), ResultsOfLength(..), FallibleResults(..),
                             AmbiguousAlternative(..), AmbiguityDecidable(..), AmbiguityWitness(..),
                             ParserFlags (ParserFlags, nullable, dependsOn),
                             Dependencies (DynamicDependencies, StaticDependencies),
                             TraceableParsing(..),
                             emptyFailure, erroneous, expected, expectedInput, replaceExpected, noFailure) where

import Control.Applicative (Applicative(..), Alternative(..))
import Data.Foldable (toList)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Const (Const)
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import Data.Monoid (Monoid(mappend, mempty))
import Data.Ord (Down(Down))
import Data.Semigroup (Semigroup((<>)))
import Data.Type.Equality ((:~:)(Refl))
import Witherable (Filterable(mapMaybe))

import Text.Grampa.Class (Ambiguous(..), FailureDescription(..), ParseFailure(..), InputParsing(..), Pos)

import Prelude hiding (length, showList)

data ResultsOfLength g s r = ResultsOfLength !Int ![(s, g (ResultList g s))] {-# UNPACK #-} !(NonEmpty r)

data ResultList g s r = ResultList ![ResultsOfLength g s r] (ParseFailure Pos s)

data BinTree a = Fork !(BinTree a) !(BinTree a)
               | Leaf !a
               | EmptyTree
               deriving (Show)

data ParserFlags g = ParserFlags {
   nullable :: Bool,
   dependsOn :: Dependencies g}

data Dependencies g = DynamicDependencies
                    | StaticDependencies (g (Const Bool))

deriving instance Show (g (Const Bool)) => Show (Dependencies g)

data AmbiguityWitness a where
   AmbiguityWitness :: (a :~: Ambiguous b) -> AmbiguityWitness a

class AmbiguityDecidable a where
   ambiguityWitness :: Maybe (AmbiguityWitness a)

instance {-# overlappable #-} AmbiguityDecidable a where
   ambiguityWitness = Nothing

instance AmbiguityDecidable (Ambiguous a) where
   ambiguityWitness = Just (AmbiguityWitness Refl)

noFailure :: ParseFailure Pos s
noFailure = emptyFailure (Down maxBound)

emptyFailure :: Pos -> ParseFailure Pos s
emptyFailure pos = ParseFailure pos (FailureDescription [] []) []

expected :: Pos -> String -> ParseFailure Pos s
expected pos msg = ParseFailure pos (FailureDescription [msg] []) []

expectedInput :: Pos -> s -> ParseFailure Pos s
expectedInput pos s = ParseFailure pos (FailureDescription [] [s]) []

erroneous :: Pos -> String -> ParseFailure Pos s
erroneous pos msg = ParseFailure pos (FailureDescription [] []) [msg]

replaceExpected :: Pos -> String -> ParseFailure Pos s -> ParseFailure Pos s
replaceExpected pos msg (ParseFailure pos' msgs errs) = ParseFailure pos' msgs' errs
   where msgs' | pos == pos' = FailureDescription [msg] []
               | otherwise = msgs

instance (Show s, Show r) => Show (ResultList g s r) where
   show (ResultList l f) = "ResultList (" ++ shows l (") (" ++ shows f ")")

instance Show s => Show1 (ResultList g s) where
   liftShowsPrec _sp showList _prec (ResultList rol f) rest = 
      "ResultList " ++ shows (simplify <$> toList rol) (shows f rest)
      where simplify (ResultsOfLength l _ r) = "ResultsOfLength " <> show l <> " _ " <> showList (toList r) ""

instance Show r => Show (ResultsOfLength g s r) where
   show (ResultsOfLength l _ r) = "(ResultsOfLength @" ++ show l ++ " " ++ shows r ")"

instance Functor (ResultsOfLength g s) where
   fmap f (ResultsOfLength l t r) = ResultsOfLength l t (f <$> r)
   {-# INLINE fmap #-}

instance Functor (ResultList g s) where
   fmap f (ResultList l failure) = ResultList ((f <$>) <$> l) failure
   {-# INLINE fmap #-}

instance Ord s => Applicative (ResultsOfLength g s) where
   pure = ResultsOfLength 0 mempty . pure
   ResultsOfLength l1 _ fs <*> ResultsOfLength l2 t2 xs = ResultsOfLength (l1 + l2) t2 (fs <*> xs)

instance Ord s => Applicative (ResultList g s) where
   pure a = ResultList [pure a] mempty
   ResultList rl1 f1 <*> ResultList rl2 f2 = ResultList ((<*>) <$> rl1 <*> rl2) (f1 <> f2)

instance Ord s => Alternative (ResultList g s) where
   empty = ResultList mempty mempty
   (<|>) = (<>)

instance Filterable (ResultList g s) where
   mapMaybe f (ResultList rols failure) = ResultList (mapMaybe maybeROL rols) failure
      where maybeROL (ResultsOfLength l t rs) = ResultsOfLength l t <$> nonEmpty (mapMaybe f $ toList rs)
   {-# INLINE mapMaybe #-}

instance Ord s => Semigroup (ResultList g s r) where
   ResultList rl1 f1 <> ResultList rl2 f2 = ResultList (merge rl1 rl2) (f1 <> f2)
      where merge [] rl = rl
            merge rl [] = rl
            merge rl1'@(rol1@(ResultsOfLength l1 s1 r1) : rest1) rl2'@(rol2@(ResultsOfLength l2 _ r2) : rest2)
               | l1 < l2 = rol1 : merge rest1 rl2'
               | l1 > l2 = rol2 : merge rl1' rest2
               | otherwise = ResultsOfLength l1 s1 (r1 <> r2) : merge rest1 rest2

instance Ord s => AmbiguousAlternative (ResultList g s) where
   ambiguousOr (ResultList rl1 f1) (ResultList rl2 f2) = ResultList (merge rl1 rl2) (f1 <> f2)
      where merge [] rl = rl
            merge rl [] = rl
            merge rl1'@(rol1@(ResultsOfLength l1 s1 r1) : rest1) rl2'@(rol2@(ResultsOfLength l2 _ r2) : rest2)
               | l1 < l2 = rol1 : merge rest1 rl2'
               | l1 > l2 = rol2 : merge rl1' rest2
               | otherwise = ResultsOfLength l1 s1 (liftA2 collect r1 r2) : merge rest1 rest2
            collect (Ambiguous xs) (Ambiguous ys) = Ambiguous (xs <> ys)

class Alternative f => AmbiguousAlternative f where
   ambiguousOr :: f (Ambiguous a) -> f (Ambiguous a) -> f (Ambiguous a)

instance Ord s => Monoid (ResultList g s r) where
   mempty = ResultList mempty mempty
   mappend = (<>)

instance Functor BinTree where
   fmap f (Fork left right) = Fork (fmap f left) (fmap f right)
   fmap f (Leaf a) = Leaf (f a)
   fmap _ EmptyTree = EmptyTree

instance Applicative BinTree where
  pure = Leaf
  EmptyTree <*> _ = EmptyTree
  Leaf f <*> t = f <$> t
  Fork f1 f2 <*> t = Fork (f1 <*> t) (f2 <*> t)

instance Foldable BinTree where
   foldMap f (Fork left right) = foldMap f left `mappend` foldMap f right
   foldMap f (Leaf a) = f a
   foldMap _ EmptyTree = mempty

instance Traversable BinTree where
   traverse f (Fork left right) = Fork <$> traverse f left <*> traverse f right
   traverse f (Leaf a) = Leaf <$> f a
   traverse _ EmptyTree = pure EmptyTree

instance Filterable BinTree where
   mapMaybe f (Fork left right) = mapMaybe f left <> mapMaybe f right
   mapMaybe f (Leaf a) = maybe EmptyTree Leaf (f a)
   mapMaybe _ EmptyTree = EmptyTree

instance Semigroup (BinTree a) where
   EmptyTree <> t = t
   t <> EmptyTree = t
   l <> r = Fork l r

instance Monoid (BinTree a) where
   mempty = EmptyTree
   mappend = (<>)

class FallibleResults f where
   hasSuccess   :: f s a -> Bool
   failureOf    :: f s a -> ParseFailure Pos s
   failWith     :: ParseFailure Pos s -> f s a

instance FallibleResults (ResultList g) where
   hasSuccess (ResultList [] _) = False
   hasSuccess _ = True
   failureOf (ResultList _ failure) = failure
   failWith = ResultList []

-- | The class of parsers whose execution can be traced for debugging purposes
class InputParsing m => TraceableParsing m where
   -- | Modify the argument parser to log its input whenever invoked.
   traceInput :: (ParserInput m -> String) -> m a -> m a
   -- | Modify the argument parser to log the given description and its input whenever invoked.
   traceAs :: Show (ParserInput m) => String -> m a -> m a
   traceAs description = traceInput (\input-> description <> " @ " <> show input)

