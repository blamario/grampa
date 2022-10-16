-- | A context-free memoizing parser that can handle left-recursive grammars.
module Text.Grampa.ContextFree.LeftRecursive
       {-# DEPRECATED "Use Text.Grampa.ContextFree.SortedMemoizing.LeftRecursive instead" #-}
       (module Text.Grampa.ContextFree.SortedMemoizing.LeftRecursive)
where

import Text.Grampa.ContextFree.SortedMemoizing.LeftRecursive
