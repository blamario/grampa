{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables #-}
module Boolean where

import Control.Applicative
import Control.Arrow (second)
import qualified Data.Bool 
import Data.Char (isSpace)
import Data.Monoid (Monoid, mappend, mempty, (<>))
import System.Environment (getArgs)

import Text.Grampa

import Prelude hiding (and, or, not)

class BooleanDomain e where
   and :: e -> e -> e
   or :: e -> e -> e
   not :: e -> e
   true :: e
   false :: e

instance BooleanDomain Bool where
   true = True
   false = False
   and = (&&)
   or = (||)
   not = Data.Bool.not

instance BooleanDomain [Char] where
   true = "True"
   false = "False"
   and = infixJoin "&&"
   or = infixJoin "||"
   not = ("not " <> )

infixJoin op a b = "(" <> a <> op <> b <> ")"

data Boolean e f =
   Boolean{
      expr :: f e,
      term :: f e,
      factor :: f e}

instance Show (f e) => Show (Boolean e f) where
   showsPrec prec a rest = "Boolean{expr=" ++ showsPrec prec (expr a)
                           (", term=" ++ showsPrec prec (term a)
                            (", factor=" ++ showsPrec prec (factor a) ("}" ++ rest)))

instance Functor1 (Boolean e) where
   fmap1 f a = a{expr= f (expr a),
                 term= f (term a),
                 factor= f (factor a)}

instance Foldable1 (Boolean e) where
   foldMap1 f a = f (expr a) <> f (term a) <> f (factor a)

instance Traversable1 (Boolean e) where
   traverse1 f a = Boolean
                   <$> f (expr a)
                   <*> f (term a)
                   <*> f (factor a)

instance Reassemblable (Boolean e) where
   composePer f g a = Boolean{expr= expr (f a{expr= expr a'}),
                              term= term (f a{term= term a'}),
                              factor= factor (f a{factor= factor a'})}
      where a' = g a
   reassemble f a = Boolean{expr= f expr a,
                            term= f term a,
                            factor= f factor a}
   reassemble' f a = Boolean{expr= f expr (\e->a{expr= e}) a,
                             term= f term (\t->a{term= t}) a,
                             factor= f factor (\f->a{factor= f}) a}

boolean :: BooleanDomain e => Grammar (Boolean e) String -> Grammar (Boolean e) String
boolean Boolean{..} = Boolean{
   expr= term
         <|> or <$> expr <* string "||" <*> term,
   term= factor
         <|> and <$> term <* string "&&" <*> factor,
   factor= string "True" *> pure true
           <|> string "False" *> pure false
           <|> string "not" *> takeCharsWhile isSpace *> (not <$> factor)
           <|> string "(" *> expr <* string ")"}

parse :: (Eq e, BooleanDomain e) => [String] -> [e]
parse s = fst <$> results ((<* endOfInput) $ expr
                          $ fmap1 feedEnd
                          $ foldr (feedGrammar g) g
                          $ reverse s)
   where g = fixGrammar boolean

parenthesize :: [String] -> [String]
parenthesize s = parse s

evaluate :: [String] -> [Bool]
evaluate s = parse s

main = getArgs >>= print . evaluate
