{-# Language FlexibleContexts, FlexibleInstances, RankNTypes, RecordWildCards, 
             ScopedTypeVariables, StandaloneDeriving, TemplateHaskell, TypeFamilies, UndecidableInstances #-}
module Main where

import Control.Applicative (Applicative, Alternative, Const(..), pure, empty, many, optional, (<*>), (*>), (<|>))
import Control.Arrow (first)
import Control.Monad (MonadPlus(mzero, mplus), guard, liftM, liftM2, void)
import Data.Char (isSpace, isLetter)
import Data.List (find, minimumBy, nub, sort)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Semigroup (Semigroup, (<>))
import Data.Monoid (Monoid(..), Product(..))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid, factors)
import Data.Monoid.Textual (TextualMonoid(toString))
import Data.Semigroup.Cancellative (LeftReductive, isPrefixOf)
import Data.Typeable (Typeable)
import Data.Word (Word8, Word64)

import Data.Functor.Compose (Compose(..))
import Text.Parser.Combinators (choice, eof, sepBy1, skipMany)
import qualified Text.Parser.Char as Char
import Text.Parser.Token (whiteSpace)

import Control.Enumerable (Shareable, Sized, share)
import Test.Feat (Enumerable(..), c0, c1, uniform)
import Test.Feat.Enumerate (pay)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Positive(..), Property,
                              (===), (==>), (.&&.), forAll, mapSize, property, sized, testProperty, within)
import Test.QuickCheck (verbose)
import Test.QuickCheck.Checkers (Binop, EqProp(..), TestBatch, unbatch)
import Test.QuickCheck.Classes (functor, monad, monoid, applicative, alternative,
                                monadFunctor, monadApplicative, monadOr, monadPlus)

import qualified Rank2
import qualified Rank2.TH
import Text.Grampa hiding (symbol)
import qualified Text.Grampa.ContextFree.Parallel as Parallel
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive

import qualified Test.Ambiguous
import qualified Test.Examples

import Prelude hiding (null, takeWhile)

data Recursive f = Recursive{start :: f String,
                             rec :: f [String],
                             one :: f String,
                             next :: f String}
deriving instance (Show (f String), Show (f [String])) => Show (Recursive f)

instance TokenParsing (LeftRecursive.Parser Recursive String)
instance LexicalParsing (LeftRecursive.Parser Recursive String)

$(Rank2.TH.deriveAll ''Recursive)

recursiveManyGrammar Recursive{..} = Recursive{
   start= optional (string "[") *> (concat <$> rec) <* optional next,
   rec= (:) <$> one <*> rec <|> pure [],
   one = string "(" *> start <* string ")",
   next= string "]"}

nameListGrammar :: Recursive (LeftRecursive.Parser Recursive String)
nameListGrammar = fixGrammar nameListGrammarBuilder
nameListGrammarBuilder g@Recursive{..} = Recursive{
   start= pure (const . unwords) <*> rec <*> (True <$ symbol "," <* symbol "..." <|> pure False) <|>
          pure id <*> symbol "..." <?> "start",
   rec= sepBy1 one (ignorable *> string "," <?> "comma") <?> "rec",
   one= do ignorable
           identifier <- ((:) <$> Char.satisfy isLetter <*> (toString (const "") <$> takeCharsWhile isLetter))
           guard (identifier /= "reserved")
           pure id <*> pure identifier
        <?> "one",
   next= string "--" *> (toString (const "") <$> takeCharsWhile (/= '\n') <* (void (char '\n') <|> eof)) <?> "next"
   }

symbol s = ignorable *> string s <* ignorable
ignorable = whiteSpace *> skipMany (nonTerminal next *> whiteSpace <?> "ignorable1") <?> "ignorable"
--ignorable = recursiveOn [next] $ whiteSpace *> skipMany (next nameListGrammar *> whiteSpace <?> "ignorable1") <?> "ignorable"
--ignorable = whiteSpace *> (Parser.NonTerminal next *> ignorable <<|> pure ())

main = defaultMain tests

type Parser = Parallel.Parser

simpleParse :: (Eq s, FactorialMonoid s, LeftReductive s) => Parallel.Parser (Rank2.Only r) s r -> s -> ParseResults s [(s, r)]
simpleParse p input = getCompose . getCompose $ simply parsePrefix p input

tests = testGroup "Grampa" [
           let g = fixGrammar recursiveManyGrammar :: Recursive (LeftRecursive.Parser Recursive String)
           in testGroup "recursive"
              [testProperty "minimal" $ start (parseComplete g "()") == Compose (Right [""]),
               testProperty "bracketed" $ start (parseComplete g "[()]") == Compose (Right [""]),
               testProperty "name list" $
                 start (parseComplete nameListGrammar "foo, bar") == Compose (Right ["foo bar"])],
           testGroup "arithmetic"
             [testProperty "arithmetic"   $ \tree-> Test.Examples.parseArithmetical (show tree) === Right tree,
              testProperty "boolean"      $ \tree-> Test.Examples.parseBoolean (show tree) === Right tree,
              testProperty "conditionals" $ \tree-> Test.Examples.parseConditional (show tree) === Right tree],
           testGroup "ambiguous"
             [testProperty "complete" $
              Test.Ambiguous.amb (parseComplete (fixGrammar Test.Ambiguous.grammar) "xyzw")
              == Compose (Right [pure (flip Test.Ambiguous.Xyzw "w" $ Ambiguous $ pure $
                                       flip Test.Ambiguous.Xyz "z" $ Ambiguous $
                                       Test.Ambiguous.Xy1 "x" "y"
                                       :| [Test.Ambiguous.Xy2
                                           (pure $ Test.Ambiguous.Xy1 "x" "") "y"])]),
              testProperty "prefix" $
              Test.Ambiguous.amb (parsePrefix (fixGrammar Test.Ambiguous.grammar) "xyzw")
              == Compose (Compose (Right [("yzw", pure (Test.Ambiguous.Xy1 "x" "")),
                                          ("zw", Ambiguous (Test.Ambiguous.Xy1 "x" "y" :|
                                                            [Test.Ambiguous.Xy2
                                                             (pure (Test.Ambiguous.Xy1 "x" ""))
                                                             "y"])),
                                          ("w", pure (Test.Ambiguous.Xyz
                                                      (Ambiguous (Test.Ambiguous.Xy1 "x" "y" :|
                                                                  [Test.Ambiguous.Xy2
                                                                   (pure (Test.Ambiguous.Xy1 "x" ""))
                                                                   "y"]))
                                                      "z")),
                                          ("", pure (flip Test.Ambiguous.Xyzw "w" $ Ambiguous $ pure $
                                                     flip Test.Ambiguous.Xyz "z" $ Ambiguous $
                                                     Test.Ambiguous.Xy1 "x" "y"
                                                     :| [Test.Ambiguous.Xy2
                                                         (pure $ Test.Ambiguous.Xy1 "x" "") "y"]))]))],
           testGroup "primitives"
             [testProperty "anyToken mempty" $ simpleParse anyToken "" == Left (ParseFailure 0 [Expected "anyToken"]),
              testProperty "anyToken list" $
                \(x::Word8) xs-> simpleParse anyToken (x:xs) == Right [(xs, [x])],
              testProperty "satisfy success" $ \bools->
                   simpleParse (satisfy head) (True:bools) == Right [(bools, [True])],
              testProperty "satisfy failure" $ \bools-> results (simpleParse (satisfy head) (False:bools)) == [],
              testProperty "satisfy mempty" $ results (simpleParse (satisfy (undefined :: [Char] -> Bool)) []) == [],
              testProperty "string success" $ \(xs::[Word8]) ys->
                   simpleParse (string xs) (xs <> ys) == Right [(ys, xs)],
              testProperty "string" $ \(xs::[Word8]) ys-> not (xs `isPrefixOf` ys)
                ==> simpleParse (string xs) ys == Left (ParseFailure 0 [ExpectedInput xs]),
              testProperty "eof mempty" $ simpleParse eof "" == Right [("", ())],
              testProperty "eof failure" $ \s->
                   s /= "" ==> simpleParse eof s == Left (ParseFailure 0 [Expected "end of input"])],
           testGroup "lookAhead"
             [testProperty "lookAhead" lookAheadP,
              testProperty "lookAhead p *> p" lookAheadConsumeP,
              testProperty "lookAhead or not" lookAheadOrNotP,
              testProperty "notFollowedBy p *> p" lookAheadNotAndP,
              testProperty "not not" lookAheadNotNotP,
              testProperty "lookAhead anyToken" lookAheadTokenP],
           testGroup "classes"
             [testBatch (((mapSize (min 10) <$>) <$>) <$> monoid parser3s),
              testBatch (functor parser3s),
              testBatch (applicative parser3s),
              testBatch (alternative parser2s),
              testBatch $ monad parser3s,
              testBatch $ monadFunctor parser2s,
              testBatch $ monadApplicative parser2s,
              -- testBatch $ monadOr parser2s,
              testBatch $ monadPlus parser2s],
           testGroup "errors"
             [testProperty "start" (Test.Examples.parseArithmetical ":4" 
                                    === Left ":4\n^\nat line 1, column 1\nexpected digits, string \"(\", or string \"-\""),
              testProperty "middle" (Test.Examples.parseArithmetical "4 - :3"
                                     === Left "4 - :3\n    ^\nat line 1, column 5\nexpected digits or string \"(\""),
              testProperty "middle line" (Test.Examples.parseArithmetical "4 -\n :3\n+ 2"
                                           === Left "4 -\n :3\n ^\nat line 2, column 2\nexpected digits or string \"(\""),
              testProperty "missing" (Test.Examples.parseArithmetical "4 - " 
                                      === Left "4 - \n    ^\nat line 1, column 5\nexpected digits or string \"(\""),
              testProperty "missing" (Test.Examples.parseArithmetical "4 -\n" 
                                      === Left "4 -\n\n^\nat line 2, column 1\nexpected digits or string \"(\"")]
           ]
   where lookAheadP :: String -> DescribedParser String [Bool] -> Bool
         lookAheadConsumeP :: DescribedParser String [Bool] -> Property
         lookAheadOrNotP :: DescribedParser String () -> Property
         lookAheadNotAndP :: DescribedParser String [Bool] -> Property
         lookAheadNotNotP :: DescribedParser String [Bool] -> Property
         lookAheadTokenP :: Char -> String -> Bool
         
         lookAheadP xs (DescribedParser _ p) = simpleParse (lookAhead p) xs
                                               == (map (first $ const xs) <$> simpleParse p xs)
         lookAheadConsumeP (DescribedParser _ p) = (lookAhead p *> p :: Parser (Rank2.Only [Bool]) String [Bool])
                                                   =-= p
         lookAheadOrNotP (DescribedParser _ p) = within 2000000 $
            (notFollowedBy p <|> lookAhead p) =-= (mempty :: Parser (Rank2.Only ()) String ())
         lookAheadNotAndP (DescribedParser _ p) = within 2000000 $
            (notFollowedBy p *> p) =-= (empty :: Parser (Rank2.Only [Bool]) String [Bool])
         lookAheadNotNotP (DescribedParser d p) =
            notFollowedBy (notFollowedBy p) =-= (void (lookAhead p) :: Parser (Rank2.Only ()) String ())
         lookAheadTokenP x xs = simpleParse (lookAhead anyToken) (x:xs) == Right [(x:xs, [x])]

instance Enumerable (DescribedParser s r) => Arbitrary (DescribedParser s r) where
   arbitrary = sized uniform

testBatch :: TestBatch -> TestTree
testBatch (label, tests) = testGroup label (uncurry testProperty . (within 5000000 <$>) <$> tests)

parser2s :: DescribedParser ([Bool], [Bool]) ([Bool], [Bool])
parser2s = undefined

parser3s :: DescribedParser ([Bool], [Bool], [Bool]) ([Bool], [Bool], [Bool])
parser3s = undefined

data DescribedParser s r = DescribedParser String (forall g. (Typeable g, Rank2.Functor g) => Parser g s r)

instance Show (DescribedParser s r) where
   show (DescribedParser d _) = d

instance (Show s, MonoidNull s, Semigroup r) => Semigroup (DescribedParser s r) where
   DescribedParser d1 p1 <> DescribedParser d2 p2 = DescribedParser (d1 ++ " <> " ++ d2) (p1 <> p2)

instance (Show s, MonoidNull s, Monoid r) => Monoid (DescribedParser s r) where
   mempty = DescribedParser "mempty" mempty
   DescribedParser d1 p1 `mappend` DescribedParser d2 p2 = DescribedParser (d1 ++ " <> " ++ d2) (mappend p1 p2)

instance EqProp (ParseFailure s) where
   ParseFailure pos1 msg1 =-= ParseFailure pos2 msg2 = property (pos1 == pos2)

instance (Ord r, Show r, EqProp r, Eq s, EqProp s, Show s, FactorialMonoid s, LeftReductive s, Arbitrary s) =>
         EqProp (Parser (Rank2.Only r) s r) where
   p1 =-= p2 = forAll arbitrary (\s-> (nub <$> simpleParse p1 s) =-= (nub <$> simpleParse p2 s))

instance (Eq s, FactorialMonoid s, LeftReductive s, Show s, EqProp s, Arbitrary s, Ord r, Show r, EqProp r, Typeable r) =>
         EqProp (DescribedParser s r) where
   DescribedParser _ p1 =-= DescribedParser _ p2 = forAll arbitrary $ \s->
      simpleParse p1 s =-= simpleParse p2 s

instance Monoid s => Functor (DescribedParser s) where
   fmap f (DescribedParser d p) = DescribedParser ("fmap ? " ++ d) (fmap f p)

instance (Show s, Monoid s) => Applicative (DescribedParser s) where
   pure x = DescribedParser "pure ?" (pure x)
   DescribedParser d1 p1 <*> DescribedParser d2 p2 = DescribedParser (d1 ++ " <*> " ++ d2) (p1 <*> p2)

instance (Show s, Monoid s) => Monad (DescribedParser s) where
   return x = DescribedParser "return ?" (return x)
   DescribedParser d1 p1 >>= f = DescribedParser (d1 ++ " >>= ?") (p1 >>= \x-> let DescribedParser _ p = f x in p)
   DescribedParser d1 p1 >> DescribedParser d2 p2 = DescribedParser (d1 ++ " >> " ++ d2) (p1 >> p2)

instance (Show s, FactorialMonoid s) => Alternative (DescribedParser s) where
   empty = DescribedParser "empty" empty
   DescribedParser d1 p1 <|> DescribedParser d2 p2 = DescribedParser (d1 ++ " <|> " ++ d2) (p1 <|> p2)

instance (Show s, FactorialMonoid s) => MonadPlus (DescribedParser s) where
   mzero = DescribedParser "mzero" mzero
   DescribedParser d1 p1 `mplus` DescribedParser d2 p2 = DescribedParser (d1 ++ " `mplus` " ++ d2) (mplus p1 p2)

instance forall s. (Semigroup s, FactorialMonoid s, LeftReductive s, Ord s, Typeable s, Show s, Enumerable s) =>
         Enumerable (DescribedParser s s) where
   enumerate = share (choice [c0 (DescribedParser "anyToken" anyToken),
                              c0 (DescribedParser "getInput" getInput),
                              c0 (DescribedParser "empty" empty),
                              c0 (DescribedParser "mempty" mempty),
                              pay (c1 $ \s-> DescribedParser "string" (string s)),
                              pay (c1 $ \pred-> DescribedParser "satisfy" (satisfy pred)),
                              pay (c1 $ \pred-> DescribedParser "takeWhile" (takeWhile pred)),
                              pay (c1 $ \pred-> DescribedParser "takeWhile1" (takeWhile1 pred)),
                              binary " *> " (*>),
                              binary " <> " (<>),
                              binary " <|> " (<|>)])

instance forall s r. (Ord s, Semigroup s, FactorialMonoid s, LeftReductive s, Show s, Enumerable s) =>
         Enumerable (DescribedParser s ()) where
   enumerate = share (choice [c0 (DescribedParser "eof" eof),
                              pay (c1 $ \(DescribedParser d p :: DescribedParser s s)-> DescribedParser ("void " <> d) (void p)),
                              pay (c1 $ \(DescribedParser d p :: DescribedParser s s)->
                                    DescribedParser ("(notFollowedBy " <> d <> ")") (notFollowedBy p))])

instance forall s r. (Show s, Semigroup s, FactorialMonoid s, Typeable s) => Enumerable (DescribedParser s [Bool]) where
   enumerate = share (choice [c0 (DescribedParser "empty" empty),
                              c0 (DescribedParser "mempty" mempty),
                              pay (c1 $ \r-> DescribedParser ("(pure " ++ shows r ")") (pure r)),
                              pay (c1 $ \(DescribedParser d p)-> DescribedParser ("(lookAhead " <> d <> ")") (lookAhead p)),
                              binary " *> " (*>),
                              binary " <> " (<>),
                              binary " <|> " (<|>)])

instance forall s r. (Show s, Semigroup s, FactorialMonoid s, Typeable s) =>
         Enumerable (DescribedParser s ([Bool] -> [Bool])) where
   enumerate = share (choice [c0 (DescribedParser "empty" empty),
                              c0 (DescribedParser "mempty" mempty),
                              pay (c1 $ \r-> DescribedParser ("(pure " ++ shows r ")") (pure r)),
                              pay (c1 $ \(DescribedParser d p)-> DescribedParser ("(lookAhead " <> d <> ")") (lookAhead p)),
                              binary " *> " (*>),
                              binary " <> " (<>),
                              binary " <|> " (<|>)])

binary :: forall f s a. (Typeable f, Sized f, Enumerable (DescribedParser s a))
       => String
       -> (forall g. Rank2.Functor g => Parser g s a -> Parser g s a -> Parser g s a)
       -> Shareable f (DescribedParser s a)
binary nm op = pay $ c1 (\(DescribedParser d1 p1, DescribedParser d2 p2)-> 
                          DescribedParser (d1 <> nm <> d2) (op p1 p2))

instance {-# OVERLAPS #-} (Ord s, Enumerable s) => Enumerable (s -> Bool) where
   enumerate = share (pay (c1 (<=)) <|> pay (c1 const))

-- instance Enumerable ([Bool] -> [Bool]) where
--    enumerate = share (choice [c0 id, c0 (map not), pay (c1 const)])

instance EqProp Word64 where
   a =-= b = property (a == b)

results = either (const []) id
