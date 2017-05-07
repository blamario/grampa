{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, RankNTypes, KindSignatures, UndecidableInstances #-}
module Main (main, arithmetic, comparisons, boolean, conditionals) where

import System.Environment (getArgs)
import Data.Functor.Compose (Compose(..))
import Data.Map (Map)
import qualified Rank2
import Text.Grampa (GrammarBuilder, ParseResults, fixGrammar)
import Text.Grampa.ContextFree.LeftRecursive (Parser, parseComplete)
import Arithmetic (Arithmetic, arithmetic)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons
import qualified Conditionals
import qualified Combined
import qualified Lambda

type ArithmeticComparisons = Rank2.Product (Arithmetic.Arithmetic Int) (Comparisons.Comparisons Int Bool)
type ArithmeticComparisonsBoolean = Rank2.Product ArithmeticComparisons (Boolean.Boolean Bool)
type ACBC = Rank2.Product ArithmeticComparisonsBoolean (Conditionals.Conditionals Bool Int)
   
main :: IO ()
main = do args <- concat <$> getArgs
          -- let a = fixGrammar (Arithmetic.arithmetic (production id Arithmetic.expr a))
          -- let a = fixGrammar (Arithmetic.arithmetic (recursive $ Arithmetic.expr a))
          print (getCompose . Lambda.expr $ parseComplete (fixGrammar Lambda.lambdaCalculus) args
                 :: ParseResults [Lambda.LambdaInitial])
          -- print (((\f-> f (mempty :: Map String Int) [1 :: Int]) <$>) <$> parseComplete (fixGrammar Lambda.lambdaCalculus) Lambda.expr args :: ParseResults Int)
          print (getCompose . Arithmetic.expr $ parseComplete (fixGrammar arithmetic) args :: ParseResults [Int])
          print (getCompose . Comparisons.test . Rank2.snd $ parseComplete (fixGrammar comparisons) args
                 :: ParseResults [Bool])
          print (getCompose . Boolean.expr . Rank2.snd $ parseComplete (fixGrammar boolean) args :: ParseResults [Bool])
          print (getCompose . Conditionals.expr . Rank2.snd $ parseComplete (fixGrammar conditionals) args
                 :: ParseResults [Int])
          print (((\f-> f (mempty :: Map String Combined.Tagged)) <$>)
                 <$> (getCompose . Combined.expr $ parseComplete (fixGrammar Combined.expression) args)
                 :: ParseResults [Combined.Tagged])

comparisons :: GrammarBuilder (Rank2.Product (Arithmetic.Arithmetic Int) (Comparisons.Comparisons Int Bool))
                              g Parser String
comparisons (Rank2.Pair a c) =
   Rank2.Pair (Arithmetic.arithmetic a) (Comparisons.comparisons c{Comparisons.term= Arithmetic.expr a})

boolean :: GrammarBuilder ArithmeticComparisonsBoolean g Parser String
boolean (Rank2.Pair ac b) = Rank2.Pair (comparisons ac) (Boolean.boolean (Comparisons.test $ Rank2.snd ac) b)

conditionals :: GrammarBuilder ACBC g Parser String
conditionals (Rank2.Pair acb c) =
   Rank2.Pair
      (boolean acb)
      (Conditionals.conditionals c{Conditionals.test= Boolean.expr (Rank2.snd acb),
                                   Conditionals.term= Arithmetic.expr (Rank2.fst $ Rank2.fst acb)})
