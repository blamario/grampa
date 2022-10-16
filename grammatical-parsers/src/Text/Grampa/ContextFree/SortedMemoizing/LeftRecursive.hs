{-# LANGUAGE ConstraintKinds, CPP, FlexibleContexts, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving, InstanceSigs,
             RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeApplications, TypeFamilies, TypeOperators,
             UndecidableInstances #-}
-- | A context-free memoizing parser that can handle ambiguous left-recursive grammars.
module Text.Grampa.ContextFree.SortedMemoizing.LeftRecursive (
   Fixed, Parser, SeparatedParser(..),
   autochain, liftPositive, liftPure, mapPrimitive,
   longest, peg, terminalPEG,
   parseSeparated, separated)
where

import Text.Grampa.Internal.LeftRecursive (Fixed(..), SeparatedParser(..),
                                           autochain, asLeaf, liftPositive, liftPure, mapPrimitive,
                                           parseSeparated, separated)
import Text.Grampa.ContextFree.SortedMemoizing (ResultList (..))
import qualified Text.Grampa.ContextFree.SortedMemoizing as Memoizing
import qualified Text.Grampa.PEG.Backtrack.Measured as Backtrack

-- | A parser for left-recursive grammars on top of the sorted memoizing 'Memoizing.Parser'. It's slightly slower than
-- the parser from "Text.Grampa.ContextFree.Memoizing.LeftRecursive" but provides more features.
type Parser = Fixed Memoizing.Parser

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
