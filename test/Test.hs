{-# Language RankNTypes, DeriveDataTypeable #-}
module Main where

import Control.Applicative (Applicative, Alternative, pure, (<*>), (*>), empty, (<|>))
import Control.Monad (MonadPlus, liftM, liftM2, mzero, mplus)
import Data.List (find, minimumBy, nub, sort)
import Data.Monoid (Monoid(..), (<>))
import Data.Typeable (Typeable)
import Data.Word (Word8)
import System.Environment (getArgs)
import Debug.Trace (trace)

import Test.Feat (Enumerable(..), Enumerate, FreePair(Free), consts, shared, unary, uniform)
import Test.Feat.Enumerate (pay)
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Positive(..), Property, testProperty, (===), (==>), (.&&.),
                              forAll, mapSize, oneof, resize, sized, whenFail)
import Test.QuickCheck (verbose)
import Test.QuickCheck.Gen (scale)
import Test.QuickCheck.Checkers (Binop, EqProp(..), TestBatch, isAssoc, leftId, rightId, verboseBatch)
import Test.QuickCheck.Classes (functor, monad, monoid, applicative, monadFunctor, monadApplicative, monadOr, monadPlus)

import Text.Grampa
import qualified Arithmetic
import qualified Comparisons
import qualified Boolean
import qualified Conditionals

main = defaultMain tests

tests = testGroup "Arithmetic" [testProperty "arithmetic" $ parseArithmetical,
                                testProperty "comparisons" $ parseComparison,
                                testProperty "boolean" $ parseBoolean,
                                testProperty "conditionals" $ parseConditional]

parseArithmetical :: Sum -> Bool
parseArithmetical (Sum s) = f s' == s'
   where f = uniqueParse (fixGrammar $ Arithmetic.arithmetic empty) Arithmetic.expr
         s' = f s

parseComparison :: Comparison -> Bool
parseComparison (Comparison s) = f s' == s'
   where f = uniqueParse (fixGrammar comparisons) (Comparisons.expr . snd1)
         s' = f s

comparisons :: Functor1 g => GrammarBuilder ArithmeticComparisons g String
comparisons (Pair a c) = Pair (Arithmetic.arithmetic empty a) (Comparisons.comparisons (Arithmetic.expr a) c)

parseBoolean :: Disjunction -> Bool
parseBoolean (Disjunction s) = f s' == s'
   where f = uniqueParse (fixGrammar boolean) (Boolean.expr . snd1)
         s' = f s

boolean :: Functor1 g => GrammarBuilder ArithmeticComparisonsBoolean g String
boolean (Pair ac b) = Pair (comparisons ac) (Boolean.boolean (Comparisons.expr $ snd1 ac) b)

parseConditional :: Conditional -> Bool
parseConditional (Conditional s) = f s' == s'
   where f = uniqueParse (fixGrammar conditionals) (Conditionals.expr . snd1)
         s' = f s

conditionals :: Functor1 g => GrammarBuilder ACBC g String
conditionals (Pair acb c) = Pair (boolean acb) (Conditionals.conditionals (Boolean.expr $ snd1 acb) (Arithmetic.expr $ fst1 $ fst1 acb) c)

type ArithmeticComparisons = Product1 (Arithmetic.Arithmetic String) (Comparisons.Comparisons String String)
type ArithmeticComparisonsBoolean = Product1 ArithmeticComparisons (Boolean.Boolean String)
type ACBC = Product1 ArithmeticComparisonsBoolean (Conditionals.Conditionals String)

newtype Factor      = Factor {factorString :: String}           deriving (Show)
newtype Product     = Product {productString :: String}         deriving (Show)
newtype Sum         = Sum {sumString :: String}                 deriving (Show)
newtype Comparison  = Comparison {compString :: String}         deriving (Show)
newtype Truth       = Truth {truthString :: String}             deriving (Show)
newtype Conjunction = Conjunction {conjunctionString :: String} deriving (Show)
newtype Disjunction = Disjunction {disjunctionString :: String} deriving (Show)
newtype Conditional = Conditional {conditionalString :: String} deriving (Show)

instance Arbitrary Factor where
   arbitrary = sized uniform
instance Arbitrary Product where
   arbitrary = sized uniform
instance Arbitrary Sum where
   arbitrary = sized uniform
instance Arbitrary Comparison where
   arbitrary = sized uniform
instance Arbitrary Truth where
   arbitrary = sized uniform
instance Arbitrary Conjunction where
   arbitrary = sized uniform
instance Arbitrary Disjunction where
   arbitrary = sized uniform
instance Arbitrary Conditional where
   arbitrary = sized uniform

instance Enumerable Factor where
   enumerate = unary (Factor . (show :: Word8 -> String))
               <> pay (unary $ Factor . (\s-> "(" <> s <> ")") . productString)

instance Enumerable Product where
   enumerate = unary (Product . factorString)
               <> (Product <$> (\(Free (Product a, Factor b))-> a <> "*" <> b) <$> pay enumerate)
               <> (Product <$> (\(Free (Product a, Factor b))-> a <> "/" <> b) <$> pay enumerate)

instance Enumerable Sum where
   enumerate = unary (Sum . productString)
               <> (Sum <$> (\(Free (Sum a, Product b))-> a <> "+" <> b) <$> pay enumerate)
               <> (Sum <$> (\(Free (Sum a, Product b))-> a <> "-" <> b) <$> pay enumerate)

instance Enumerable Comparison where
   enumerate = Comparison <$> (((\(Free (Sum a, Sum b))-> a <> "<" <> b) <$> pay enumerate)
                               <> ((\(Free (Sum a, Sum b))-> a <> "<=" <> b) <$> pay enumerate)
                               <> ((\(Free (Sum a, Sum b))-> a <> "==" <> b) <$> pay enumerate)
                               <> ((\(Free (Sum a, Sum b))-> a <> ">=" <> b) <$> pay enumerate)
                               <> ((\(Free (Sum a, Sum b))-> a <> ">" <> b) <$> pay enumerate))

instance Enumerable Truth where
   enumerate = Truth <$> (consts [pure "False", pure "True"]
                          <> pay (unary $ ("not " <>) . truthString)
                          <> pay (unary $ (\s-> "(" <> s <> ")") . disjunctionString))

instance Enumerable Conjunction where
   enumerate = unary (Conjunction . truthString)
               <> (Conjunction <$> (\(Free (Conjunction a, Truth b))-> a <> "&&" <> b) <$> pay enumerate)

instance Enumerable Disjunction where
   enumerate = unary (Disjunction . conjunctionString)
               <> (Disjunction <$> (\(Free (Disjunction a, Conjunction b))-> a <> "||" <> b) <$> pay enumerate)

instance Enumerable Conditional where
   enumerate = Conditional
               <$> (\(Free (Disjunction a, Free (Sum b, Sum c)))-> "if " <> a <> " then " <> b <> " else " <> c)
               <$> pay enumerate

uniqueParse :: (FactorialMonoid s, Alternative1 g, Reassemblable g, Traversable1 g) =>
               Grammar g s -> (forall f. g f -> f r) -> s -> r
uniqueParse g p s = case parseAll g p s
                    of [r] -> r
                       [] -> error "Unparseable"
                       _ -> error "Ambiguous"
