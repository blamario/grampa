{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables, TemplateHaskell #-}
module Boolean where

import Control.Applicative
import qualified Data.Bool
import Data.Char (isSpace)
import Data.Monoid ((<>))

import qualified Rank2
import Text.Grampa
import Utilities (infixJoin, keyword, symbol)

import Rank2.TH

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

data Boolean e f =
   Boolean{
      expr :: f e,
      term :: f e,
      factor :: f e}

instance Show (f e) => Show (Boolean e f) where
   showsPrec prec a rest = "Boolean{expr=" ++ showsPrec prec (expr a)
                           (", term=" ++ showsPrec prec (term a)
                            (", factor=" ++ showsPrec prec (factor a) ("}" ++ rest)))

$(deriveFunctor ''Boolean)

{-
instance Rank2.Functor (Boolean e) where
   fmap f a = a{expr= f (expr a),
                term= f (term a),
                factor= f (factor a)}
-}

instance Rank2.Apply (Boolean e) where
   ap a a' = Boolean (expr a `Rank2.apply` expr a') (term a `Rank2.apply` term a') (factor a `Rank2.apply` factor a')

instance Rank2.Alternative (Boolean e) where
   empty = Boolean empty empty empty
   choose a a' = Boolean{expr = expr a <|> expr a',
                         term = term a <|> term a',
                         factor = factor a <|> factor a'}

instance Rank2.Foldable (Boolean e) where
   foldMap f a = f (expr a) <> f (term a) <> f (factor a)

instance Rank2.Traversable (Boolean e) where
   traverse f a = Boolean
                  <$> f (expr a)
                  <*> f (term a)
                  <*> f (factor a)

instance Rank2.Reassemblable (Boolean e) where
   reassemble f a = Boolean{expr= f expr a,
                            term= f term a,
                            factor= f factor a}

boolean :: (BooleanDomain e, Rank2.Functor g) => Parser g String e -> GrammarBuilder (Boolean e) g String
boolean p Boolean{..} = Boolean{
   expr= term
         <|> or <$> expr <* symbol "||" <*> term,
   term= factor
         <|> and <$> term <* symbol "&&" <*> factor,
   factor= keyword "True" *> pure true
           <|> keyword "False" *> pure false
           <|> keyword "not" *> takeCharsWhile isSpace *> (not <$> factor)
           <|> p
           <|> symbol "(" *> expr <* symbol ")"}
