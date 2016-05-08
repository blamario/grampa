module Main (main) where

import System.Environment (getArgs)
import Text.Grampa (Functor1, Grammar, GrammarBuilder, Parser, Production, Product1(Pair, fst1, snd1),
                    fixGrammar, parse, production)
import Arithmetic (Arithmetic, arithmetic)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons
import qualified Conditionals

type ArithmeticComparisons = Product1 (Arithmetic.Arithmetic Int) (Comparisons.Comparisons Int Bool)
   
main = do args <- getArgs
          print (parse Arithmetic.arithmetic expr args :: [Int])
          print (parse comparisons (Comparisons.expr . snd1) args :: [Bool])
          print (parse boolean Boolean.expr args :: [Bool])
          print (parse conditionals Conditionals.expr args :: [Int])
          -- print (parse (Combined.expression id) Combined.expr args :: [Combined.Tagged])
   where expr = Arithmetic.expr :: Production (Arithmetic Int) p Int
         boolean = Boolean.boolean comparisons (Comparisons.expr . snd1)
         boolean2 = Boolean.boolean comparisons (Comparisons.expr . snd1)
         conditionals = Conditionals.conditionals boolean2 Boolean.expr Arithmetic.arithmetic Arithmetic.expr

comparisons :: Functor1 g => GrammarBuilder ArithmeticComparisons g String
comparisons (Pair a c) = Pair (Arithmetic.arithmetic a) (Comparisons.comparisons (Arithmetic.expr a) c)
