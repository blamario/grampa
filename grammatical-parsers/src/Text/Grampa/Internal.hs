module Text.Grampa.Internal (BinTree(..), FailureInfo(..)) where

import Data.Monoid (Monoid(mappend, mempty), (<>))
import Data.Word (Word64)

data FailureInfo = FailureInfo !Int Word64 [String] deriving (Eq, Show)

data BinTree a = Fork !(BinTree a) !(BinTree a)
               | Leaf !a
               | EmptyTree
               deriving (Show)

instance Monoid FailureInfo where
   mempty = FailureInfo 0 maxBound []
   f1@(FailureInfo s1 pos1 exp1) `mappend` f2@(FailureInfo s2 pos2 exp2)
      | s1 < s2 = f2
      | s1 > s2 = f1
      | otherwise = FailureInfo s1 pos' exp'
      where (pos', exp') | pos1 < pos2 = (pos1, exp1)
                         | pos1 > pos2 = (pos2, exp2)
                         | otherwise = (pos1, exp1 <> exp2)

instance Functor BinTree where
   fmap f (Fork left right) = Fork (fmap f left) (fmap f right)
   fmap f (Leaf a) = Leaf (f a)
   fmap _ EmptyTree = EmptyTree

instance Foldable BinTree where
   foldMap f (Fork left right) = foldMap f left <> foldMap f right
   foldMap f (Leaf a) = f a
   foldMap _ EmptyTree = mempty

instance Monoid (BinTree a) where
   mempty = EmptyTree
   mappend EmptyTree t = t
   mappend t EmptyTree = t
   mappend l r = Fork l r
