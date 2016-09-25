{-# Language FlexibleContexts, FlexibleInstances, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Main where

import Control.Applicative (Applicative, Alternative, pure, (<*>), (*>), empty, (<|>))
import Control.Monad (MonadPlus(mzero, mplus), liftM, liftM2, void)
import Data.List (find, minimumBy, nub, sort)
import Data.Monoid (Monoid(..), Product(..), (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid(..))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(factors))
import Data.Typeable (Typeable)
import Data.Word (Word8)

import Test.Feat (Enumerable(..), Enumerate, FreePair(Free), consts, shared, unary, uniform)
import Test.Feat.Enumerate (pay)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Positive(..), Property,
                              (===), (==>), (.&&.), forAll, property, sized, testProperty, within)
import Test.QuickCheck.Checkers (Binop, EqProp(..), TestBatch, unbatch)
import Test.QuickCheck.Classes (functor, monad, monoid, applicative, alternative,
                                monadFunctor, monadApplicative, monadOr, monadPlus)

import Text.Grampa

import qualified Test.Examples

import Prelude hiding (null, takeWhile)

main = defaultMain tests

tests = testGroup "Grampa"
          [testGroup "arithmetic"
             [testProperty "arithmetic"   $ Test.Examples.parseArithmetical,
              testProperty "comparisons"  $ Test.Examples.parseComparison,
              testProperty "boolean"      $ Test.Examples.parseBoolean,
              testProperty "conditionals" $ Test.Examples.parseConditional],
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
           testGroup "lookAhead"
             [testProperty "lookAhead" lookAheadP,
              testProperty "lookAhead p *> p" lookAheadConsumeP,
              testProperty "lookAhead or not" lookAheadOrNotP,
              testProperty "notFollowedBy p *> p" lookAheadNotAndP,
              testProperty "not not" lookAheadNotNotP,
              testProperty "lookAhead anyToken" lookAheadTokenP],
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
             ]]
   where lookAheadP :: String -> DescribedParser String [Bool] -> Bool
         lookAheadConsumeP :: DescribedParser String [Bool] -> Property
         lookAheadOrNotP :: DescribedParser String () -> Property
         lookAheadNotAndP :: DescribedParser String [Bool] -> Property
         lookAheadNotNotP :: DescribedParser String [Bool] -> Property
         lookAheadTokenP :: Char -> String -> Bool
         
         lookAheadP xs (DescribedParser _ p) =
            simpleParse (lookAhead p) xs == map (const xs <$>) (simpleParse p xs)
         lookAheadConsumeP (DescribedParser _ p) = (lookAhead p *> p :: Parser (Singleton1 [Bool]) String [Bool]) =-= p
         lookAheadOrNotP (DescribedParser _ p) = within 2000000 $
            (notFollowedBy p <|> lookAhead p) =-= (mempty :: Parser (Singleton1 ()) String ())
         lookAheadNotAndP (DescribedParser _ p) = within 2000000 $
            (notFollowedBy p *> p) =-= (empty :: Parser (Singleton1 [Bool]) String [Bool])
         lookAheadNotNotP (DescribedParser d p) =
            notFollowedBy (notFollowedBy p) =-= (void (lookAhead p) :: Parser (Singleton1 ()) String ())
         lookAheadTokenP x xs = simpleParse (lookAhead anyToken) (x:xs) == [([x], x:xs)]

instance Enumerable (DescribedParser s r) => Arbitrary (DescribedParser s r) where
   arbitrary = sized uniform

testBatch :: TestBatch -> TestTree
testBatch (label, tests) = testGroup label (uncurry testProperty <$> tests)

parser2s :: DescribedParser ([Bool], [Bool]) ([Bool], [Bool])
parser2s = undefined

parser3s :: DescribedParser ([Bool], [Bool], [Bool]) ([Bool], [Bool], [Bool])
parser3s = undefined

data DescribedParser s r = DescribedParser String (forall g. (Typeable g, Functor1 g) => Parser g s r)

instance Show (DescribedParser s r) where
   show (DescribedParser d _) = d

instance (MonoidNull s, Monoid r) => Monoid (DescribedParser s r) where
   mempty = DescribedParser "mempty" mempty
   DescribedParser d1 p1 `mappend` DescribedParser d2 p2 = DescribedParser (d1 ++ " <> " ++ d2) (mappend p1 p2)

instance (Ord r, Show r, EqProp r, Eq s, EqProp s, Show s, FactorialMonoid s, Arbitrary s) =>
         EqProp (Parser (Singleton1 r) s r) where
   p1 =-= p2 = forAll arbitrary (\s-> nub (simpleParse p1 s) =-= nub (simpleParse p2 s))

instance (FactorialMonoid s, Show s, EqProp s, Arbitrary s, Ord r, Show r, EqProp r, Typeable r) =>
         EqProp (DescribedParser s r) where
   DescribedParser _ p1 =-= DescribedParser _ p2 = forAll arbitrary (\s-> simpleParse p1 s =-= simpleParse p2 s)

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

instance forall s. (FactorialMonoid s, LeftReductiveMonoid s, Ord s, Typeable s, Show s, Enumerable s) =>
         Enumerable (DescribedParser s s) where
   enumerate = consts (pure <$> [DescribedParser "anyToken" anyToken,
                                 DescribedParser "getInput" getInput,
                                 DescribedParser "empty" empty,
                                 DescribedParser "mempty" mempty])
               <> pay (unary $ \t-> DescribedParser "token" (token t))
               <> pay (unary $ \s-> DescribedParser "string" (string s))
               <> pay (unary $ \pred-> DescribedParser "satisfy" (satisfy pred))
               <> pay (unary $ \pred-> DescribedParser "takeWhile" (takeWhile pred))
               <> pay (unary $ \pred-> DescribedParser "takeWhile1" (takeWhile1 pred))
               <> binary " *> " (*>)
               <> binary " <> " (<>)
               <> binary " <|> " (<|>)
      where binary :: String -> (forall g. Functor1 g => Parser g s s -> Parser g s s -> Parser g s s)
                   -> Enumerate (DescribedParser s s)
            binary nm op = (\(Free (DescribedParser d1 p1, DescribedParser d2 p2))-> DescribedParser (d1 <> nm <> d2) (op p1 p2))
                           <$> pay enumerate

instance forall s r. (Ord s, FactorialMonoid s, LeftReductiveMonoid s, Show s, Enumerable s) =>
         Enumerable (DescribedParser s ()) where
   enumerate = consts (pure <$> [DescribedParser "endOfInput" endOfInput])
               <> pay (unary $ \(DescribedParser d p :: DescribedParser s s)-> DescribedParser ("void " <> d) (void p))
               <> pay (unary $ \(DescribedParser d p :: DescribedParser s s)->
                                  DescribedParser ("(notFollowedBy " <> d <> ")") (notFollowedBy p))

instance forall s r. (FactorialMonoid s, Typeable s) => Enumerable (DescribedParser s [Bool]) where
   enumerate = consts (pure <$> [DescribedParser "empty" empty,
                                 DescribedParser "mempty" mempty])
               <> pay (unary $ \r-> DescribedParser ("(pure " ++ shows r ")") (pure r))
               <> pay (unary $ \(DescribedParser d p)-> DescribedParser ("(lookAhead " <> d <> ")") (lookAhead p))
               <> binary " *> " (*>)
               <> binary " <> " (<>)
               <> binary " <|> " (<|>)
      where binary :: String -> (forall g. Functor1 g => Parser g s [Bool] -> Parser g s [Bool] -> Parser g s [Bool])
                   -> Enumerate (DescribedParser s [Bool])
            binary nm op = (\(Free (DescribedParser d1 p1, DescribedParser d2 p2))-> DescribedParser (d1 <> nm <> d2) (op p1 p2))
                           <$> pay enumerate

instance forall s r. (FactorialMonoid s, Typeable s) => Enumerable (DescribedParser s ([Bool] -> [Bool])) where
   enumerate = consts (pure <$> [DescribedParser "empty" empty,
                                 DescribedParser "mempty" mempty])
               <> pay (unary $ \r-> DescribedParser ("(pure " ++ shows r ")") (pure r))
               <> pay (unary $ \(DescribedParser d p)-> DescribedParser ("(lookAhead " <> d <> ")") (lookAhead p))
               <> binary " *> " (*>)
               <> binary " <> " (<>)
               <> binary " <|> " (<|>)
      where binary :: String -> (forall g. Functor1 g => Parser g s ([Bool] -> [Bool]) -> Parser g s ([Bool] -> [Bool])
                                 -> Parser g s ([Bool] -> [Bool]))
                   -> Enumerate (DescribedParser s ([Bool] -> [Bool]))
            binary nm op = (\(Free (DescribedParser d1 p1, DescribedParser d2 p2))-> DescribedParser (d1 <> nm <> d2) (op p1 p2))
                           <$> pay enumerate

instance (Ord s, Enumerable s) => Enumerable (s -> Bool) where
   enumerate = pay (unary (<=))
               <> pay (unary const)

instance Enumerable ([Bool] -> [Bool]) where
   enumerate = consts [pure id,
                       pure (map not)]
               <> pay (unary const)

uniqueParse :: (FactorialMonoid s, Alternative1 g, Reassemblable g, Traversable1 g) =>
               Grammar g s -> (forall f. g f -> f r) -> s -> r
uniqueParse g p s = case parseAll g p s
                    of [r] -> r
                       [] -> error "Unparseable"
                       _ -> error "Ambiguous"
