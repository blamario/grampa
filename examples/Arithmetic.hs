{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables #-}
module Arithmetic where

import Control.Applicative
import Data.Char (isDigit, isSpace)
import Data.Monoid ((<>))

import Text.Grampa
import Utilities (infixJoin, symbol)

import qualified Rank2
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

instance Rank2.Functor (Arithmetic e) where
   fmap f a = a{expr= f (expr a),
                term= f (term a),
                factor= f (factor a)}

instance Rank2.Apply (Arithmetic e) where
   ap a a' = Arithmetic (expr a `Rank2.apply` expr a')
                        (term a `Rank2.apply` term a')
                        (factor a `Rank2.apply` factor a')

instance Rank2.Applicative (Arithmetic e) where
   pure f = Arithmetic f f f

instance Rank2.Distributive (Arithmetic e) where
   distribute f = Arithmetic{expr= f >>= expr,
                             term= f >>= term,
                             factor= f >>= factor}

instance Rank2.Foldable (Arithmetic e) where
   foldMap f a = f (expr a) <> f (term a) <> f (factor a)

instance Rank2.Traversable (Arithmetic e) where
   traverse f a = Arithmetic
                  <$> f (expr a)
                  <*> f (term a)
                  <*> f (factor a)

arithmetic :: (Rank2.Functor g, ArithmeticDomain e) => Parser g String e -> GrammarBuilder (Arithmetic e) g String
arithmetic sub Arithmetic{..} = Arithmetic{
   expr= term
         <|> symbol "-" *> (negate <$> term)
         <|> add <$> expr <* symbol "+" <*> term
         <|> subtract <$> expr <* symbol "-" <*> term,
   term= factor
         <|> multiply <$> term <* symbol "*" <*> factor
         <|> divide <$> term <* symbol "/" <*> factor,
   factor= skipCharsWhile isSpace *> ((number . read) <$> takeCharsWhile1 isDigit <?> "digits")
           <|> sub
           <|> symbol "(" *> expr <* symbol ")"}
