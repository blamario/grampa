{-# Language FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
module Test.Examples where

import Control.Applicative (empty, liftA2, liftA3, (<|>))
import Data.Functor.Compose (Compose(..))
import Data.Monoid (Monoid(..), (<>))
import Data.Monoid.Textual (TextualMonoid, toString)
import Text.Parser.Combinators (choice)

import Test.Tasty.QuickCheck (Arbitrary(..), Gen, NonNegative(..), Property, testProperty, (===), (==>), (.&&.),
                              elements, forAll, mapSize, oneof, resize, sized, whenFail)
import Data.Word (Word8)

import qualified Rank2
import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive (Parser)
import qualified Arithmetic
import qualified Comparisons
import qualified Boolean
import qualified Conditionals

parseArithmetical :: String -> Either String ArithmeticTree   
parseArithmetical = uniqueParse (fixGrammar Arithmetic.arithmetic) Arithmetic.expr

parseBoolean :: String -> Either String BooleanTree
parseBoolean = uniqueParse (fixGrammar boolean) (Boolean.expr . Rank2.snd)

comparisons :: (Rank2.Functor g, LexicalParsing (Parser g String)) =>
               GrammarBuilder ArithmeticComparisons g Parser String
comparisons (Rank2.Pair a c) =
   Rank2.Pair (Arithmetic.arithmetic a) (Comparisons.comparisons c){Comparisons.term= Arithmetic.expr a}

boolean :: (Rank2.Functor g, LexicalParsing (Parser g String)) =>
           GrammarBuilder ArithmeticComparisonsBoolean g Parser String
boolean (Rank2.Pair ac b) = Rank2.Pair (comparisons ac) (Boolean.boolean (Comparisons.test $ Rank2.snd ac) b)

parseConditional :: String -> Either String (ConditionalTree ArithmeticTree)
parseConditional = uniqueParse (fixGrammar conditionals) (Conditionals.expr . Rank2.snd)

conditionals :: (Rank2.Functor g, LexicalParsing (Parser g String)) => GrammarBuilder ACBC g Parser String
conditionals (Rank2.Pair acb c) =
   boolean acb `Rank2.Pair`
   Conditionals.conditionals c{Conditionals.test= Boolean.expr (Rank2.snd acb),
                               Conditionals.term= Unconditional <$> Arithmetic.expr (Rank2.fst $ Rank2.fst acb)}

type ArithmeticComparisons = Rank2.Product (Arithmetic.Arithmetic ArithmeticTree) (Comparisons.Comparisons ArithmeticTree BooleanTree)
type ArithmeticComparisonsBoolean = Rank2.Product ArithmeticComparisons (Boolean.Boolean BooleanTree)
type ACBC = Rank2.Product ArithmeticComparisonsBoolean (Conditionals.Conditionals BooleanTree
                                                        (ConditionalTree ArithmeticTree))

data ArithmeticTree = Number (NonNegative Int)
                    | Add ArithmeticTree ArithmeticTree
                    | Multiply ArithmeticTree ArithmeticTree
                    | Negate ArithmeticTree
                    | Subtract ArithmeticTree ArithmeticTree
                    | Divide ArithmeticTree ArithmeticTree
                    deriving Eq

data BooleanTree = BooleanConstant Bool
                 | Comparison ArithmeticTree Relation ArithmeticTree
                 | Not BooleanTree
                 | And BooleanTree BooleanTree
                 | Or BooleanTree BooleanTree
                 deriving Eq

data ConditionalTree a = If BooleanTree (ConditionalTree a) (ConditionalTree a)
                       | Unconditional a
                       deriving Eq

newtype Relation = Relation String deriving Eq

instance Show ArithmeticTree where
   showsPrec p (Add l r) rest | p < 1 = showsPrec 0 l (" + " <> showsPrec 1 r rest)
   showsPrec p (Subtract l r) rest | p < 1 = showsPrec 0 l (" - " <> showsPrec 1 r rest)
   showsPrec p (Negate e) rest | p < 1 = "- " <> showsPrec 1 e rest
   showsPrec p (Multiply l r) rest | p < 2 = showsPrec 1 l (" * " <> showsPrec 2 r rest)
   showsPrec p (Divide l r) rest | p < 2 = showsPrec 1 l (" / " <> showsPrec 2 r rest)
   showsPrec _ (Number (NonNegative n)) rest = shows n rest
   showsPrec p e rest = "(" <> showsPrec 0 e (")" <> rest)

instance Show BooleanTree where
   showsPrec p (Or l r) rest | p < 1 = showsPrec 1 l (" || " <> showsPrec 0 r rest)
   showsPrec p (And l r) rest | p < 2 = showsPrec 2 l (" && " <> showsPrec 1 r rest)
   showsPrec p (Not e) rest | p < 3 = "not " <> showsPrec 3 e rest
   showsPrec p (Comparison l rel r) rest | p < 3 = showsPrec 0 l (" " <> show rel <> " " <> showsPrec 0 r rest)
   showsPrec _ (BooleanConstant b) rest = shows b rest
   showsPrec p e rest = "(" <> showsPrec 0 e (")" <> rest)

instance Show a => Show (ConditionalTree a) where
   show (Unconditional a) = show a
   show (If test true false) = "if " <> show test <> " then " <> show true <> " else " <> show false

instance Show Relation where
   show (Relation rel) = rel

instance Arithmetic.ArithmeticDomain ArithmeticTree where
   number = Number . NonNegative
   add = Add
   multiply = Multiply
   negate = Negate
   subtract = Subtract
   divide = Divide

instance Boolean.BooleanDomain BooleanTree where
   true = BooleanConstant True
   false = BooleanConstant False
   and = And
   or = Or
   not = Not

instance Comparisons.ComparisonDomain ArithmeticTree BooleanTree where
   lessThan = flip Comparison (Relation "<")
   lessOrEqual = flip Comparison (Relation "<=")
   equal = flip Comparison (Relation "==")
   greaterOrEqual = flip Comparison (Relation ">=")
   greaterThan = flip Comparison (Relation ">")

instance Conditionals.ConditionalDomain BooleanTree (ConditionalTree ArithmeticTree) where
   ifThenElse = If

instance Arbitrary ArithmeticTree where
   arbitrary = sized tree
     where tree n | n < 1 = Number <$> arbitrary
                  | otherwise = oneof [Number <$> arbitrary,
                                       Negate <$> tree (n - 1),
                                       liftA2 Add branch branch,
                                       liftA2 Multiply branch branch,
                                       liftA2 Subtract branch branch,
                                       liftA2 Divide branch branch]
             where branch = tree (n `div` 2)

instance Arbitrary BooleanTree where
   arbitrary = sized tree
     where tree n | n < 1 = BooleanConstant <$> arbitrary
                  | otherwise = oneof [BooleanConstant <$> resize (n - 1) arbitrary,
                                       Not <$> tree (n - 1),
                                       liftA3 Comparison arbitrary' (elements relations) arbitrary',
                                       liftA2 And branch branch,
                                       liftA2 Or branch branch]
             where branch = tree (n `div` 2)
                   relations = Relation <$> ["<", ">", "==", "<=", ">="]
                   arbitrary' = resize (n `div` 2) arbitrary

instance Arbitrary (ConditionalTree ArithmeticTree) where
   arbitrary = sized tree
     where tree n = oneof [--Unconditional <$> resize (n - 1) arbitrary,
                           liftA3 If (resize (n `div` 3) arbitrary)
                                     (Unconditional <$> resize(n `div` 3) arbitrary)
                                     (Unconditional <$> resize(n `div` 3) arbitrary)]

uniqueParse :: (Ord s, TextualMonoid s, Show r, Rank2.Apply g, Rank2.Traversable g, Rank2.Distributive g) =>
               Grammar g Parser s -> (forall f. g f -> f r) -> s -> Either String r
uniqueParse g p s = case getCompose (p $ parseComplete g s)
                    of Right [r] -> Right r
                       Right [] -> Left "Unparseable"
                       Right rs -> Left ("Ambiguous: " ++ show rs)
                       Left err -> Left (toString mempty $ failureDescription s err 3)

instance TokenParsing (Parser ArithmeticComparisons String) where
   token = lexicalToken
instance TokenParsing (Parser ArithmeticComparisonsBoolean String) where
   token = lexicalToken
instance TokenParsing (Parser ACBC String) where
   token = lexicalToken

instance LexicalParsing (Parser ArithmeticComparisons String)
instance LexicalParsing (Parser ArithmeticComparisonsBoolean String)
instance LexicalParsing (Parser ACBC String)

