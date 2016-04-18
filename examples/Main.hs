module Main (main) where

import Text.Grampa (Grammar, Parser)
import qualified Arithmetic (Arithmetic, arithmetic, expr, main)
import qualified Boolean (main)
import qualified Comparisons (Comparisons, main)

main = Arithmetic.main
       >> Boolean.main
       >> Comparisons.main (Arithmetic.expr :: Arithmetic.Arithmetic Int p -> p Int) Arithmetic.arithmetic
