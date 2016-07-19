{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables #-}
module Arithmetic where

import Control.Applicative
import Data.Char (isDigit, isSpace)
import Data.Monoid ((<>))

import Text.Grampa
import Utilities (infixJoin, symbol)

import Prelude hiding (negate, subtract)

class ArithmeticDomain e where
   number :: Int -> e
   add :: e -> e -> e
   multiply :: e -> e -> e
   negate :: e -> e
   subtract :: e -> e -> e
   divide :: e -> e -> e

instance ArithmeticDomain Int where
   number = id
   add = (+)
   multiply = (*)
   negate = (0 -)
   subtract = (-)
   divide = div

instance ArithmeticDomain [Char] where
   number = show
   add = infixJoin "+"
   multiply = infixJoin "*"
   negate = ("-" <>)
   subtract = infixJoin "-"
   divide = infixJoin "/"

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

instance Apply1 (Arithmetic e) where
   ap1 a a' = Arithmetic (expr a `apply1` expr a') (term a `apply1` term a') (factor a `apply1` factor a')

instance Alternative1 (Arithmetic e) where
   empty1 = Arithmetic empty empty empty
   choose1 a a' = Arithmetic{expr = expr a <|> expr a',
                             term = term a <|> term a',
                             factor = factor a <|> factor a'}

instance Foldable1 (Arithmetic e) where
   foldMap1 f a = f (expr a) <> f (term a) <> f (factor a)

instance Traversable1 (Arithmetic e) where
   traverse1 f a = Arithmetic
                   <$> f (expr a)
                   <*> f (term a)
                   <*> f (factor a)

instance Reassemblable (Arithmetic e) where
   reassemble f a = Arithmetic{expr= f expr a,
                               term= f term a,
                               factor= f factor a}

arithmetic :: (ArithmeticDomain e, Functor1 g) => Parser g String e -> GrammarBuilder (Arithmetic e) g String
arithmetic sub Arithmetic{..} = Arithmetic{
   expr= term
         <|> symbol "-" *> (negate <$> term)
         <|> add <$> expr <* symbol "+" <*> term
         <|> subtract <$> expr <* symbol "-" <*> term,
   term= factor
         <|> multiply <$> term <* symbol "*" <*> factor
         <|> divide <$> term <* symbol "/" <*> factor,
   factor= skipCharsWhile isSpace *> ((number . read) <$> takeCharsWhile1 isDigit)
           <|> sub
           <|> symbol "(" *> expr <* symbol ")"}
