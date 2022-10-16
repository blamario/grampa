{-# LANGUAGE FlexibleContexts, FlexibleInstances, RankNTypes, KindSignatures, UndecidableInstances #-}
module Main (main, arithmetic, comparisons, boolean, conditionals) where

import System.Environment (getArgs)
import Data.Functor.Compose (Compose(..))
import Data.Map (Map)
import qualified Rank2
import Text.Grampa (TokenParsing, LexicalParsing, GrammarBuilder, ParseResults, fixGrammar, parseComplete)
import Text.Grampa.ContextFree.SortedMemoizing.LeftRecursive (Parser)
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
                 :: ParseResults String [Lambda.LambdaInitial])
          -- print (((\f-> f (mempty :: Map String Int) [1 :: Int]) <$>) <$> parse (fixGrammar Lambda.lambdaCalculus) Lambda.expr args :: ParseResults String Int)
          print (getCompose . Arithmetic.expr $ parseComplete (fixGrammar arithmetic) args :: ParseResults String [Int])
          print (getCompose . Comparisons.test . Rank2.snd $ parseComplete (fixGrammar comparisons) args
                 :: ParseResults String [Bool])
          print (getCompose . Boolean.expr . Rank2.snd $
                 parseComplete (fixGrammar boolean) args :: ParseResults String [Bool])
          print (getCompose . Conditionals.expr . Rank2.snd $ parseComplete (fixGrammar conditionals) args
                 :: ParseResults String [Int])
          print (((\f-> f (mempty :: Map String Combined.Tagged)) <$>)
                 <$> (getCompose . Combined.expr $ parseComplete (fixGrammar Combined.expression) args)
                 :: ParseResults String [Combined.Tagged])

comparisons :: (LexicalParsing (Parser g String)) => GrammarBuilder ArithmeticComparisons g Parser String
comparisons (Rank2.Pair a c) =
   Rank2.Pair (Arithmetic.arithmetic a) (Comparisons.comparisons c{Comparisons.term= Arithmetic.expr a})

boolean :: (LexicalParsing (Parser g String)) => GrammarBuilder ArithmeticComparisonsBoolean g Parser String
boolean (Rank2.Pair ac b) = Rank2.Pair (comparisons ac) (Boolean.boolean (Comparisons.test $ Rank2.snd ac) b)

conditionals :: (LexicalParsing (Parser g String)) => GrammarBuilder ACBC g Parser String
conditionals (Rank2.Pair acb c) =
   Rank2.Pair
      (boolean acb)
      (Conditionals.conditionals c{Conditionals.test= Boolean.expr (Rank2.snd acb),
                                   Conditionals.term= Arithmetic.expr (Rank2.fst $ Rank2.fst acb)})

instance TokenParsing (Parser ArithmeticComparisons String)
instance TokenParsing (Parser ArithmeticComparisonsBoolean String)
instance TokenParsing (Parser ACBC String)
instance TokenParsing (Parser (Lambda.Lambda Lambda.LambdaInitial) String)

instance LexicalParsing (Parser ArithmeticComparisons String)
instance LexicalParsing (Parser ArithmeticComparisonsBoolean String)
instance LexicalParsing (Parser ACBC String)
instance LexicalParsing (Parser (Lambda.Lambda Lambda.LambdaInitial) String)

