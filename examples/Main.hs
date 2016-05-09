module Main (main) where

import Control.Applicative (empty)
import System.Environment (getArgs)
import Text.Grampa (Functor1, Grammar, GrammarBuilder, Parser, Production, Product1(Pair, fst1, snd1),
                    fixGrammar, parse, production)
import Arithmetic (Arithmetic, arithmetic)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons
import qualified Conditionals
import qualified Combined

type ArithmeticComparisons = Product1 (Arithmetic.Arithmetic Int) (Comparisons.Comparisons Int Bool)
type ArithmeticComparisonsBoolean = Product1 ArithmeticComparisons (Boolean.Boolean Bool)
type ACBC = Product1 ArithmeticComparisonsBoolean (Conditionals.Conditionals Int)
   
main = do args <- getArgs
          print (parse (Arithmetic.arithmetic empty) Arithmetic.expr args :: [Int])
          print (parse comparisons (Comparisons.expr . snd1) args :: [Bool])
          print (parse boolean (Boolean.expr . snd1) args :: [Bool])
          print (parse conditionals (Conditionals.expr .snd1) args :: [Int])
          print (parse (Combined.expression id) Combined.expr args :: [Combined.Tagged])
   where expr = Arithmetic.expr :: Production (Arithmetic Int) p Int

comparisons :: Functor1 g => GrammarBuilder ArithmeticComparisons g String
comparisons (Pair a c) = Pair (Arithmetic.arithmetic empty a) (Comparisons.comparisons (Arithmetic.expr a) c)

boolean :: Functor1 g => GrammarBuilder ArithmeticComparisonsBoolean g String
boolean (Pair ac b) = Pair (comparisons ac) (Boolean.boolean (Comparisons.expr $ snd1 ac) b)

conditionals :: Functor1 g => GrammarBuilder ACBC g String
conditionals (Pair acb c) = Pair (boolean acb) (Conditionals.conditionals (Boolean.expr $ snd1 acb) (Arithmetic.expr $ fst1 $ fst1 acb) c)
