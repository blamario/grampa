-- | A context-free parser that can handle left-recursive grammars and carry a
-- monadic computation with each parsing result.
module Text.Grampa.ContextFree.LeftRecursive.Transformer
       {-# DEPRECATED "Use Text.Grampa.ContextFree.SortedMemoizing.Transformer.LeftRecursive instead" #-}
       (module Text.Grampa.ContextFree.SortedMemoizing.Transformer.LeftRecursive)
where

import Text.Grampa.ContextFree.SortedMemoizing.Transformer.LeftRecursive
