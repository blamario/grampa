{-# Language FlexibleInstances, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables #-}
module Main where

import Control.Applicative (Applicative, Alternative, pure, (<*>), (*>), empty, (<|>))
import Control.Monad (MonadPlus(mzero, mplus), liftM, liftM2, void)
import Data.List (find, isPrefixOf, minimumBy, nub, sort)
import Data.Monoid (Monoid(..), (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid)
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(factors))
import Data.Typeable (Typeable)
import Data.Word (Word8)
import System.Environment (getArgs)
import Debug.Trace (trace)

import Test.Feat (Enumerable(..), Enumerate, FreePair(Free), consts, shared, unary, uniform)
import Test.Feat.Enumerate (pay)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Positive(..), Property, testProperty, (===), (==>), (.&&.),
                              forAll, mapSize, oneof, resize, sized, whenFail)
import Test.QuickCheck (verbose)
import Test.QuickCheck.Gen (scale)
import Test.QuickCheck.Checkers (Binop, EqProp(..), TestBatch, isAssoc, leftId, rightId, unbatch, verboseBatch)
import Test.QuickCheck.Classes (functor, monad, monoid, applicative, alternative,
                                monadFunctor, monadApplicative, monadOr, monadPlus)

import Text.Grampa
import qualified Arithmetic
import qualified Comparisons
import qualified Boolean
import qualified Conditionals

import Prelude hiding (null)

main = defaultMain tests

tests = testGroup "Grampa"
          [testGroup "arithmetic"
             [testProperty "arithmetic" $ parseArithmetical,
              testProperty "comparisons" $ parseComparison,
              testProperty "boolean" $ parseBoolean,
              testProperty "conditionals" $ parseConditional],
           testGroup "primitives"
             [testProperty "anyToken mempty" $ simpleParse anyToken "" == [],
              testProperty "anyToken list" $ \(x::Word8) xs-> simpleParse anyToken (x:xs) == [([x],xs)],
              testProperty "token success" $ \(x::Word8) xs-> simpleParse (token [x]) (x:xs) == [([x],xs)],
              testProperty "token failure" $ \(x::Word8) y xs-> x /= y ==> simpleParse (token [y]) (x:xs) == [],
              testProperty "token mempty" $ \x-> simpleParse (token [x]) "" == [],
              testProperty "satisfy success" $ \bools-> simpleParse (satisfy head) (True:bools) == [([True], bools)],
              testProperty "satisfy failure" $ \bools-> simpleParse (satisfy head) (False:bools) == [],
              testProperty "satisfy mempty" $ simpleParse (satisfy (undefined :: [Char] -> Bool)) [] == [],
              testProperty "string success" $ \(xs::[Word8]) ys-> simpleParse (string xs) (xs <> ys) == [(xs, ys)],
              testProperty "string" $ \(xs::[Word8]) ys-> not (xs `isPrefixOf` ys) ==> simpleParse (string xs) ys == [],
              testProperty "endOfInput mempty" $ simpleParse endOfInput "" == [((),"")],
              testProperty "endOfInput failure" $ \s-> s /= "" ==> simpleParse endOfInput s == []],
          testGroup "classes"
             [testBatch (monoid parser3s),
              testBatch (functor parser3s),
              testBatch (applicative parser3s),
              testBatch (alternative parser2s),
              testBatch $ monad parser3s,
              testBatch $ monadFunctor parser2s,
              testBatch $ monadApplicative parser2s,
              -- testBatch $ monadOr parser2s,
              testBatch $ monadPlus parser2s
              {-,
              testProperty "lookAhead" $ lookAheadBatch,
              testProperty "join" $ testJoin
              -}
             ]]

testBatch :: TestBatch -> TestTree
testBatch (label, tests) = testGroup label (uncurry testProperty <$> tests)

instance (MonoidNull a, MonoidNull b, MonoidNull c) => MonoidNull (a, b, c) where
   null (a, b, c) = null a && null b && null c

instance (FactorialMonoid a, FactorialMonoid b, FactorialMonoid c) => FactorialMonoid (a, b, c) where
   factors (a, b, c) = [(a1, b1, c1) | a1 <- factors a, b1 <- factors b, c1 <- factors c]

parser2s :: DescribedParser ([Bool], [Bool]) ([Bool], [Bool])
parser2s = undefined

parser3s :: DescribedParser ([Bool], [Bool], [Bool]) ([Bool], [Bool], [Bool])
parser3s = undefined

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
instance forall s r. (FactorialMonoid s, Typeable s, Eq s, Show r, Monoid r, Enumerable r) =>
         Arbitrary (DescribedParser s r) where
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

data DescribedParser s r = DescribedParser String (forall g. (Typeable g, Functor1 g) => Parser g s r)

instance Show (DescribedParser s r) where
   show (DescribedParser d _) = d

instance (MonoidNull s, Monoid r) => Monoid (DescribedParser s r) where
   mempty = DescribedParser "mempty" mempty
   DescribedParser d1 p1 `mappend` DescribedParser d2 p2 = DescribedParser (d1 ++ " <> " ++ d2) (mappend p1 p2)

instance (Ord r, Show r, EqProp r, EqProp s, Show s, FactorialMonoid s, Arbitrary s) =>
         EqProp (Parser (Singleton1 r) s r) where
   p1 =-= p2 = forAll (sized $ \n-> resize (min n 20) arbitrary)
                      (\s-> --whenFail (print (s, p1, p2))
                                     parse (Singleton1 p1) getSingle s =-= parse (Singleton1 p2) getSingle s)

instance (FactorialMonoid s, Show s, EqProp s, Arbitrary s, Ord r, Show r, EqProp r, Typeable r) =>
         EqProp (DescribedParser s r) where
   DescribedParser _ p1 =-= DescribedParser _ p2 =
      forAll arbitrary (\s-> parse (Singleton1 p1) getSingle s =-= parse (Singleton1 p2) getSingle s)

instance Monoid s => Functor (DescribedParser s) where
   fmap f (DescribedParser d p) = DescribedParser ("fmap ? " ++ d) (fmap f p)

instance Monoid s => Applicative (DescribedParser s) where
   pure x = DescribedParser "pure ?" (pure x)
   DescribedParser d1 p1 <*> DescribedParser d2 p2 = DescribedParser (d1 ++ " <*> " ++ d2) (p1 <*> p2)

instance Monoid s => Monad (DescribedParser s) where
   return x = DescribedParser "return ?" (return x)
   DescribedParser d1 p1 >>= f = DescribedParser (d1 ++ " >>= ?") (p1 >>= \x-> let DescribedParser _ p = f x in p)
   DescribedParser d1 p1 >> DescribedParser d2 p2 = DescribedParser (d1 ++ " >> " ++ d2) (p1 >> p2)

instance Monoid s => Alternative (DescribedParser s) where
   empty = DescribedParser "empty" empty
   DescribedParser d1 p1 <|> DescribedParser d2 p2 = DescribedParser (d1 ++ " <|> " ++ d2) (p1 <|> p2)

instance Monoid s => MonadPlus (DescribedParser s) where
   mzero = DescribedParser "mzero" mzero
   DescribedParser d1 p1 `mplus` DescribedParser d2 p2 = DescribedParser (d1 ++ " `mplus` " ++ d2) (mplus p1 p2)

--instance Enumerable (DescribedParser [Bool] [Bool]) where
instance forall s. (FactorialMonoid s, LeftReductiveMonoid s, Typeable s, Eq s, Show s, Enumerable s) =>
         Enumerable (DescribedParser s s) where
   enumerate = consts (pure <$> [DescribedParser "anyToken" anyToken])
--                                 DescribedParser "satisfy" (satisfy head)])
               <> pay (unary $ \t-> DescribedParser "token" (token t))
               <> pay (unary $ \s-> DescribedParser "string" (string s))

instance forall s r. (FactorialMonoid s, Typeable s, Eq s) => Enumerable (DescribedParser s ()) where
   enumerate = consts (pure <$> [DescribedParser "endOfInput" endOfInput])
--               <> pay (unary $ \(DescribedParser d p)-> DescribedParser ("void " <> d) (void p))
--               <> pay (unary $ \(DescribedParser d p)-> DescribedParser ("notFollowedBy " <> d) (notFollowedBy p))

instance forall s r. (FactorialMonoid s, Typeable s, Eq s, Show r, Monoid r, Enumerable r) =>
         Enumerable (DescribedParser s r) where
   enumerate = consts (pure <$> [DescribedParser "empty" empty,
                                 DescribedParser "mempty" mempty])
               <> pay (unary $ \r-> DescribedParser ("(pure " ++ shows r ")") (pure r))
               <> pay (unary $ \(DescribedParser d p)-> DescribedParser ("lookAhead " <> d) (lookAhead p))
               <> binary " *> " (*>)
               <> binary " <> " (<>)
               <> binary " <|> " (<|>)
      where binary :: String -> (forall g. (Functor1 g, Typeable g) => Parser g s r -> Parser g s r -> Parser g s r) -> Enumerate (DescribedParser s r)
            binary nm op = (\(Free (DescribedParser d1 p1, DescribedParser d2 p2))-> DescribedParser (d1 <> nm <> d2) (op p1 p2))
                           <$> pay enumerate

instance Enumerable r => Enumerable ([Bool] -> r) where
   enumerate = pay (unary const)

uniqueParse :: (FactorialMonoid s, Alternative1 g, Reassemblable g, Traversable1 g) =>
               Grammar g s -> (forall f. g f -> f r) -> s -> r
uniqueParse g p s = case parseAll g p s
                    of [r] -> r
                       [] -> error "Unparseable"
                       _ -> error "Ambiguous"

simpleParse :: FactorialMonoid s => Parser (Singleton1 a) s a -> s -> [(a, s)]
simpleParse p s = parse (Singleton1 p) getSingle s
