module Main (main) where

import System.Environment (getArgs)
import Text.Grampa (Grammar, Parser, Production, parse)
import Arithmetic (Arithmetic, arithmetic)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons

main = do args <- getArgs
          print (parse Arithmetic.arithmetic expr args :: [Int])
          print (parse comparisons1 Comparisons.expr args :: [Bool])
          print (parse boolean Boolean.expr args :: [Bool])
   where expr = Arithmetic.expr :: Production (Arithmetic Int) p Int
         comparisons1 = Comparisons.comparisons arithmetic expr
         comparisons2 = Comparisons.comparisons arithmetic expr
         boolean = Boolean.boolean comparisons2 Comparisons.expr
