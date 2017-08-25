module Text.Grampa.Internal (FailureInfo(..)) where

import Data.Monoid (Monoid(mappend, mempty), (<>))
import Data.Word (Word64)

data FailureInfo = FailureInfo !Int Word64 [String] deriving (Eq, Show)

instance Monoid FailureInfo where
   mempty = FailureInfo 0 maxBound []
   f1@(FailureInfo s1 pos1 exp1) `mappend` f2@(FailureInfo s2 pos2 exp2)
      | s1 < s2 = f2
      | s1 > s2 = f1
      | otherwise = FailureInfo s1 pos' exp'
      where (pos', exp') | pos1 < pos2 = (pos1, exp1)
                         | pos1 > pos2 = (pos2, exp2)
                         | otherwise = (pos1, exp1 <> exp2)

