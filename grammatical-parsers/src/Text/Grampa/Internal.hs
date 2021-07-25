{-# LANGUAGE ConstrainedClassMethods, FlexibleContexts, FlexibleInstances, GADTs, RankNTypes, TypeOperators #-}

module Text.Grampa.Internal (BinTree(..), FailureInfo(..), ResultList(..), ResultsOfLength(..), FallibleResults(..),
                             AmbiguousAlternative(..), AmbiguityDecidable(..), AmbiguityWitness(..),
                             TraceableParsing(..),
                             fromResultList, noFailure) where

import Control.Applicative (Applicative(..), Alternative(..))
import Data.Foldable (toList)
import Data.Functor.Classes (Show1(..))
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import Data.List (nub)
import Data.Monoid (Monoid(mappend, mempty))
import Data.Ord (Down(Down))
import Data.Semigroup (Semigroup((<>)))
import Data.Type.Equality ((:~:)(Refl))
import Witherable (Filterable(mapMaybe))

import Data.Monoid.Factorial (FactorialMonoid, length)

import Text.Grampa.Class (Ambiguous(..), Expected(..), ParseFailure(..), ParseResults, InputParsing(..))

import Prelude hiding (length, showList)

data FailureInfo s = FailureInfo (Down Int) [Expected s] deriving (Eq, Show)

data ResultsOfLength g s r = ResultsOfLength !Int ![(s, g (ResultList g s))] !(NonEmpty r)

data ResultList g s r = ResultList ![ResultsOfLength g s r] !(FailureInfo s)

data BinTree a = Fork !(BinTree a) !(BinTree a)
               | Leaf !a
               | EmptyTree
               deriving (Show)

data AmbiguityWitness a where
   AmbiguityWitness :: (a :~: Ambiguous b) -> AmbiguityWitness a

class AmbiguityDecidable a where
   ambiguityWitness :: Maybe (AmbiguityWitness a)

instance {-# overlappable #-} AmbiguityDecidable a where
   ambiguityWitness = Nothing

instance AmbiguityDecidable (Ambiguous a) where
   ambiguityWitness = Just (AmbiguityWitness Refl)

fromResultList :: (Eq s, FactorialMonoid s) => s -> ResultList g s r -> ParseResults s [(s, r)]
fromResultList s (ResultList [] (FailureInfo pos msgs)) = Left (ParseFailure (fromIntegral $ pos - 1) (nub msgs))
fromResultList _ (ResultList rl _failure) = Right (foldMap f rl)
   where f (ResultsOfLength _ ((s, _):_) r) = (,) s <$> toList r
         f (ResultsOfLength _ [] r) = (,) mempty <$> toList r
{-# INLINABLE fromResultList #-}

noFailure :: FailureInfo s
noFailure = FailureInfo maxBound []

instance Semigroup (FailureInfo s) where
   FailureInfo pos1 exp1 <> FailureInfo pos2 exp2 = FailureInfo pos' exp'
      where (pos', exp') | pos1 > pos2 = (pos1, exp1)
                         | pos1 < pos2 = (pos2, exp2)
                         | otherwise = (pos1, exp1 <> exp2)

instance Monoid (FailureInfo s) where
   mempty = FailureInfo maxBound []
   mappend = (<>)

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

instance Applicative (ResultsOfLength g s) where
   pure = ResultsOfLength 0 mempty . pure
   ResultsOfLength l1 _ fs <*> ResultsOfLength l2 t2 xs = ResultsOfLength (l1 + l2) t2 (fs <*> xs)

instance Applicative (ResultList g s) where
   pure a = ResultList [pure a] mempty
   ResultList rl1 f1 <*> ResultList rl2 f2 = ResultList ((<*>) <$> rl1 <*> rl2) (f1 <> f2)

instance Alternative (ResultList g s) where
   empty = ResultList mempty mempty
   (<|>) = (<>)

instance Filterable (ResultList g s) where
   mapMaybe f (ResultList l failure) = ResultList (mapMaybe maybeROL l) failure
      where maybeROL (ResultsOfLength l t rs) = ResultsOfLength l t <$> nonEmpty (mapMaybe f $ toList rs)
   {-# INLINE mapMaybe #-}

instance Semigroup (ResultList g s r) where
   ResultList rl1 f1 <> ResultList rl2 f2 = ResultList (merge rl1 rl2) (f1 <> f2)
      where merge [] rl = rl
            merge rl [] = rl
            merge rl1'@(rol1@(ResultsOfLength l1 s1 r1) : rest1) rl2'@(rol2@(ResultsOfLength l2 _ r2) : rest2)
               | l1 < l2 = rol1 : merge rest1 rl2'
               | l1 > l2 = rol2 : merge rl1' rest2
               | otherwise = ResultsOfLength l1 s1 (r1 <> r2) : merge rest1 rest2

instance AmbiguousAlternative (ResultList g s) where
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

instance Monoid (ResultList g s r) where
   mempty = ResultList mempty mempty
   mappend = (<>)

instance Functor BinTree where
   fmap f (Fork left right) = Fork (fmap f left) (fmap f right)
   fmap f (Leaf a) = Leaf (f a)
   fmap _ EmptyTree = EmptyTree

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
   failureOf    :: f s a -> FailureInfo s
   failWith     :: FailureInfo s -> f s a

instance FallibleResults (ResultList g) where
   hasSuccess (ResultList [] _) = False
   hasSuccess _ = True
   failureOf (ResultList _ failure) = failure
   failWith = ResultList []

class InputParsing m => TraceableParsing m where
   traceInput :: (ParserInput m -> String) -> m a -> m a
   traceAs :: Show (ParserInput m) => String -> m a -> m a
   traceAs description = traceInput (\input-> description <> " @ " <> show input)

