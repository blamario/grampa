{-# Language RankNTypes, ScopedTypeVariables #-}
module Test.Examples where

import Control.Applicative (empty, (<|>))
import Data.Monoid (Monoid(..), (<>))
import Data.Word (Word8)

import Test.Feat (Enumerable(..), Enumerate, FreePair(Free), consts, shared, unary, uniform)
import Test.Feat.Enumerate (pay)
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Positive(..), Property, testProperty, (===), (==>), (.&&.),
                              forAll, mapSize, oneof, resize, sized, whenFail)

import qualified Rank2
import Text.Grampa
import qualified Arithmetic
import qualified Comparisons
import qualified Boolean
import qualified Conditionals

parseArithmetical :: Sum -> Bool
parseArithmetical (Sum s) = f s' == s'
   where f = uniqueParse (fixGrammarAnalysis $ Arithmetic.arithmetic empty) Arithmetic.expr
         s' = f s

parseComparison :: Comparison -> Bool
parseComparison (Comparison s) = f s' == s'
   where f = uniqueParse (fixGrammarAnalysis comparisons) (Comparisons.test . Rank2.snd)
         s' = f s

comparisons :: Rank2.Functor g => GrammarBuilder ArithmeticComparisons g Analysis String
comparisons (Rank2.Pair a c) =
   Rank2.Pair (Arithmetic.arithmetic empty a) (Comparisons.comparisons (Arithmetic.expr a) c)

parseBoolean :: Disjunction -> Bool
parseBoolean (Disjunction s) = f s' == s'
   where f = uniqueParse (fixGrammarAnalysis boolean) (Boolean.expr . Rank2.snd)
         s' = f s

boolean :: Rank2.Functor g => GrammarBuilder ArithmeticComparisonsBoolean g Analysis String
boolean (Rank2.Pair ac b) = Rank2.Pair (comparisons ac) (Boolean.boolean (Comparisons.test $ Rank2.snd ac) b)

parseConditional :: Conditional -> Bool
parseConditional (Conditional s) = f s' == s'
   where f = uniqueParse (fixGrammarAnalysis conditionals) (Conditionals.expr . Rank2.snd)
         s' = f s

conditionals :: Rank2.Functor g => GrammarBuilder ACBC g Analysis String
conditionals (Rank2.Pair acb c) =
   boolean acb `Rank2.Pair`
   Conditionals.conditionals (Boolean.expr $ Rank2.snd acb) (Arithmetic.expr $ Rank2.fst $ Rank2.fst acb) c

type ArithmeticComparisons = Rank2.Product (Arithmetic.Arithmetic String) (Comparisons.Comparisons String String)
type ArithmeticComparisonsBoolean = Rank2.Product ArithmeticComparisons (Boolean.Boolean String)
type ACBC = Rank2.Product ArithmeticComparisonsBoolean (Conditionals.Conditionals String)

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

uniqueParse :: (FactorialMonoid s, Rank2.Apply g, Rank2.Traversable g, Rank2.Distributive g) =>
               Grammar g Analysis s -> (forall f. g f -> f r) -> s -> r
uniqueParse g p s = case parseAll g p s
                    of Right [r] -> r
                       Right [] -> error "Unparseable"
                       Right _ -> error "Ambiguous"
                       Left (pos, exp) -> error ("At " <> show pos <> " expected one of " <> show exp)
