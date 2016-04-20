module Main (main) where

import Text.Grampa (Grammar, Parser, Production)
import Arithmetic (Arithmetic, arithmetic)
import Comparisons (Comparisons, comparisons)
import qualified Arithmetic (expr, main)
import qualified Boolean (main)
import qualified Comparisons (expr, main)

main = Arithmetic.main
       >> Comparisons.main expr arithmetic
       >> Boolean.main (Comparisons.expr :: Production (Comparisons (Arithmetic Int) Bool) p Bool) (comparisons expr arithmetic)
   where expr = Arithmetic.expr :: Production (Arithmetic Int) p Int
