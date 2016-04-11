{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables #-}
module Main where

import Control.Applicative
import Control.Arrow (second)
import Data.Char (isDigit)
import Data.Monoid (Monoid, mappend, mempty, (<>))
import System.Environment (getArgs)

import Text.Grampa

import Prelude hiding (subtract)

class Expression e where
   number :: Int -> e
   add :: e -> e -> e
   multiply :: e -> e -> e
   subtract :: e -> e -> e
   divide :: e -> e -> e

instance Expression Int where
   number = id
   add = (+)
   multiply = (*)
   subtract = (-)
   divide = div

instance Expression [Char] where
   number = show
   add = infixJoin "+"
   multiply = infixJoin "*"
   subtract = infixJoin "-"
   divide = infixJoin "/"

infixJoin op a b = "(" <> a <> op <> b <> ")"

data Arithmetic e f =
   Arithmetic{
      expr :: f e,
      term :: f e,
      factor :: f e}

instance Show (f e) => Show (Arithmetic e f) where
   showsPrec prec a rest = "Arithmetic{expr=" ++ showsPrec prec (expr a)
                           (", term=" ++ showsPrec prec (term a)
                            (", factor=" ++ showsPrec prec (factor a) ("}" ++ rest)))

instance Functor1 (Arithmetic e) where
   fmap1 f a = a{expr= f (expr a),
                 term= f (term a),
                 factor= f (factor a)}

instance Foldable1 (Arithmetic e) where
   foldMap1 f a = f (expr a) <> f (term a) <> f (factor a)

instance Traversable1 (Arithmetic e) where
   traverse1 f a = Arithmetic
                   <$> f (expr a)
                   <*> f (term a)
                   <*> f (factor a)

instance Reassemblable (Arithmetic e) where
   composePer f g a = Arithmetic{expr= expr (f a{expr= expr a'}),
                                 term= term (f a{term= term a'}),
                                 factor= factor (f a{factor= factor a'})}
      where a' = g a
   reassemble f a = Arithmetic{expr= f expr a,
                               term= f term a,
                               factor= f factor a}
   reassemble' f a = Arithmetic{expr= f expr (\e->a{expr= e}) a,
                                term= f term (\t->a{term= t}) a,
                                factor= f factor (\f->a{factor= f}) a}

arithmetic :: forall e. Expression e =>
              Arithmetic e (Parser (Arithmetic e) String) -> Arithmetic e (Parser (Arithmetic e) String)

arithmetic Arithmetic{..} = Arithmetic{
   expr= term
         <|> add <$> expr <* string "+" <*> term
         <|> subtract <$> expr <* string "-" <*> term,
   term= factor
         <|> multiply <$> term <* string "*" <*> factor
         <|> divide <$> term <* string "/" <*> factor,
   factor= ((number . read) <$> takeCharsWhile1 isDigit)
           <|> string "(" *> expr <* string ")"}
arithmetic' Arithmetic{..} = Arithmetic{
   expr= term
         `iterateMany` (\expr'-> add <$> expr' <* string "+" <*> term
                                 <|> subtract <$> expr' <* string "-" <*> term),
   term= factor
         `iterateMany` (\term'-> multiply <$> term' <* string "*" <*> factor
                                 <|> divide <$> term' <* string "/" <*> factor),
   factor= ((number . read) <$> takeCharsWhile1 isDigit)
           <|> string "(" *> expr <* string ")"}

parse :: (Eq e, Expression e) => [String] -> [(e, String)]
parse s = second inputWith <$> results (expr $ fmap1 feedEof
                                       $ foldr (feedGrammar g) g
                                       $ reverse s)
   where g = fixGrammar arithmetic

parenthesize :: [String] -> [(String, String)]
parenthesize s = parse s

evaluate :: [String] -> [(Int, String)]
evaluate s = parse s

main = getArgs >>= print . evaluate
