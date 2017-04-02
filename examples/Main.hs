{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, RankNTypes, KindSignatures, UndecidableInstances #-}
module Main (main, arithmetic, comparisons, boolean, conditionals) where

import Control.Applicative (empty)
import System.Environment (getArgs)
import qualified Rank2
import Text.Grampa (Grammar, GrammarBuilder, AST, ParseResults, Parsing, MonoidParsing, fixGrammarAST, parseAll)
import Arithmetic (Arithmetic, arithmetic)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons
import qualified Conditionals
import qualified Combined

type ArithmeticComparisons = Rank2.Product (Arithmetic.Arithmetic Int) (Comparisons.Comparisons Int Bool)
type ArithmeticComparisonsBoolean = Rank2.Product ArithmeticComparisons (Boolean.Boolean Bool)
type ACBC = Rank2.Product ArithmeticComparisonsBoolean (Conditionals.Conditionals Int)
   
main :: IO ()
main = do args <- concat <$> getArgs
          -- let a = fixGrammar (Arithmetic.arithmetic (production id Arithmetic.expr a))
          -- let a = fixGrammar (Arithmetic.arithmetic (recursive $ Arithmetic.expr a))
          print (parseAll (fixGrammarAST $ arithmetic empty) Arithmetic.expr args :: ParseResults Int)
          print (parseAll (fixGrammarAST comparisons) (Comparisons.test . Rank2.snd) args :: ParseResults Bool)
          print (parseAll (fixGrammarAST boolean) (Boolean.expr . Rank2.snd) args :: ParseResults Bool)
          print (parseAll (fixGrammarAST conditionals) (Conditionals.expr . Rank2.snd) args :: ParseResults Int)
          print (parseAll (fixGrammarAST Combined.expression) Combined.expr args :: ParseResults Combined.Tagged)

comparisons :: GrammarBuilder (Rank2.Product (Arithmetic.Arithmetic Int) (Comparisons.Comparisons Int Bool)) g AST String
comparisons (Rank2.Pair a c) =
   Rank2.Pair (Arithmetic.arithmetic empty a) (Comparisons.comparisons (Arithmetic.expr a) c)

boolean :: GrammarBuilder ArithmeticComparisonsBoolean g AST String
boolean (Rank2.Pair ac b) = Rank2.Pair (comparisons ac) (Boolean.boolean (Comparisons.test $ Rank2.snd ac) b)

conditionals :: GrammarBuilder ACBC g AST String
conditionals (Rank2.Pair acb c) =
   Rank2.Pair
      (boolean acb)
      (Conditionals.conditionals (Boolean.expr $ Rank2.snd acb) (Arithmetic.expr $ Rank2.fst $ Rank2.fst acb) c)
