module Main (main) where

import Control.Applicative (empty)
import Data.Word (Word64)
import System.Environment (getArgs)
import Text.Grampa (Functor1, Grammar, GrammarBuilder, Parser, ParseResults, Product1(Pair, fst1, snd1),
                    fixGrammar, parseAll)
import Arithmetic (Arithmetic, arithmetic)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons
import qualified Conditionals
import qualified Combined

type ArithmeticComparisons = Product1 (Arithmetic.Arithmetic Int) (Comparisons.Comparisons Int Bool)
type ArithmeticComparisonsBoolean = Product1 ArithmeticComparisons (Boolean.Boolean Bool)
type ACBC = Product1 ArithmeticComparisonsBoolean (Conditionals.Conditionals Int)
   
main = do args <- concat <$> getArgs
          -- let a = fixGrammar (Arithmetic.arithmetic (production id Arithmetic.expr a))
          -- let a = fixGrammar (Arithmetic.arithmetic (recursive $ Arithmetic.expr a))
          print (parseAll (fixGrammar $ arithmetic empty) Arithmetic.expr args :: ParseResults Int)
          print (parseAll (fixGrammar comparisons) (Comparisons.expr . snd1) args :: ParseResults Bool)
          print (parseAll (fixGrammar boolean) (Boolean.expr . snd1) args :: ParseResults Bool)
          print (parseAll (fixGrammar conditionals) (Conditionals.expr . snd1) args :: ParseResults Int)
          print (parseAll (fixGrammar $ Combined.expression id) Combined.expr args :: ParseResults Combined.Tagged)

comparisons :: Functor1 g => GrammarBuilder ArithmeticComparisons g String
comparisons (Pair a c) = Pair (Arithmetic.arithmetic empty a) (Comparisons.comparisons (Arithmetic.expr a) c)

boolean :: Functor1 g => GrammarBuilder ArithmeticComparisonsBoolean g String
boolean (Pair ac b) = Pair (comparisons ac) (Boolean.boolean (Comparisons.expr $ snd1 ac) b)

conditionals :: Functor1 g => GrammarBuilder ACBC g String
conditionals (Pair acb c) = Pair (boolean acb) (Conditionals.conditionals (Boolean.expr $ snd1 acb) (Arithmetic.expr $ fst1 $ fst1 acb) c)
