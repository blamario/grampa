module Main (main) where

import Text.Grampa (Grammar, Parser)
import qualified Arithmetic (Arithmetic, arithmetic, expr, main)
import qualified Boolean (main)
import qualified Comparisons (Comparisons, comparisons, expr, main)

main = Arithmetic.main
       >> Comparisons.main (Arithmetic.expr :: Arithmetic.Arithmetic Int p -> p Int) Arithmetic.arithmetic
       >> Boolean.main (Comparisons.expr :: Comparisons.Comparisons (Arithmetic.Arithmetic Int) Bool p -> p Bool) (Comparisons.comparisons (Arithmetic.expr :: Arithmetic.Arithmetic Int p -> p Int) Arithmetic.arithmetic)
