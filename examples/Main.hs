{-# LANGUAGE PartialTypeSignatures #-}

module Main (main) where

import System.Environment (getArgs)
import Text.Grampa (Grammar, GrammarBuilder, Parser, Production, parse)
import Arithmetic (Arithmetic, arithmetic)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons
import qualified Conditionals

main = do args <- getArgs
          print (parse Arithmetic.arithmetic expr args :: [Int])
          print (parse comparisons1 Comparisons.expr args :: [Bool])
          print (parse boolean Boolean.expr args :: [Bool])
          print (parse conditionals Conditionals.expr args :: [Int])
   where expr = Arithmetic.expr :: Production (Arithmetic Int) p Int
         comparisons1 = Comparisons.comparisons arithmetic expr
         comparisons2 = Comparisons.comparisons arithmetic expr
         comparisons3 = Comparisons.comparisons arithmetic expr :: GrammarBuilder (Comparisons.Comparisons _ Bool) _ String
         boolean = Boolean.boolean comparisons2 Comparisons.expr
         boolean2 = Boolean.boolean comparisons3 Comparisons.expr
         conditionals = Conditionals.conditionals boolean2 Boolean.expr Arithmetic.arithmetic Arithmetic.expr
