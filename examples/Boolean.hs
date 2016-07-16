{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables #-}
module Boolean where

import Control.Applicative
import qualified Data.Bool
import Data.Char (isSpace)
import Data.Monoid ((<>))

import Text.Grampa
import Utilities (infixJoin, keyword, symbol)

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

instance Functor1 (Boolean e) where
   fmap1 f a = a{expr= f (expr a),
                 term= f (term a),
                 factor= f (factor a)}

instance Apply1 (Boolean e) where
   ap1 a a' = Boolean (expr a `apply1` expr a') (term a `apply1` term a') (factor a `apply1` factor a')

instance Alternative1 (Boolean e) where
   empty1 = Boolean empty empty empty
   choose1 a a' = Boolean{expr = expr a <|> expr a',
                             term = term a <|> term a',
                             factor = factor a <|> factor a'}

instance Foldable1 (Boolean e) where
   foldMap1 f a = f (expr a) <> f (term a) <> f (factor a)

instance Traversable1 (Boolean e) where
   traverse1 f a = Boolean
                   <$> f (expr a)
                   <*> f (term a)
                   <*> f (factor a)

instance Reassemblable (Boolean e) where
   applyFieldwise f a b = Boolean{expr= expr (f b{expr= expr a}),
                                  term= term (f b{term= term a}),
                                  factor= factor (f b{factor= factor a})}
   reassemble f a = Boolean{expr= f expr (\e->a{expr= e}) a,
                            term= f term (\t->a{term= t}) a,
                            factor= f factor (\f->a{factor= f}) a}

boolean :: (BooleanDomain e, Functor1 g) => Parser g String e -> GrammarBuilder (Boolean e) g String
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
