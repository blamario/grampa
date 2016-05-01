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

data Boolean g e f =
   Boolean{
      expr :: f e,
      term :: f e,
      factor :: f e,
      subgrammar :: g f}

instance (Show (f e), Show (g f)) => Show (Boolean g e f) where
   showsPrec prec a rest = "Boolean{expr=" ++ showsPrec prec (expr a)
                           (", term=" ++ showsPrec prec (term a)
                            (", factor=" ++ showsPrec prec (factor a) ("}" ++ rest)))

instance Functor1 g => Functor1 (Boolean g e) where
   fmap1 f a = a{expr= f (expr a),
                 term= f (term a),
                 factor= f (factor a),
                 subgrammar= fmap1 f (subgrammar a)}

instance Foldable1 g => Foldable1 (Boolean g e) where
   foldMap1 f a = f (expr a) <> f (term a) <> f (factor a) <> foldMap1 f (subgrammar a)

instance Traversable1 g => Traversable1 (Boolean g e) where
   traverse1 f a = Boolean
                   <$> f (expr a)
                   <*> f (term a)
                   <*> f (factor a)
                   <*> traverse1 f (subgrammar a)

instance Reassemblable g => Reassemblable (Boolean g e) where
   applyFieldwise f a b = Boolean{expr= expr (f b{expr= expr a}),
                                  term= term (f b{term= term a}),
                                  factor= factor (f b{factor= factor a}),
                                  subgrammar= applyFieldwise f' (subgrammar a) (subgrammar b)}
      where f' c = subgrammar (f $ b{subgrammar= c})
   reassemble f a = Boolean{expr= f expr (\e->a{expr= e}) a,
                            term= f term (\t->a{term= t}) a,
                            factor= f factor (\f->a{factor= f}) a,
                            subgrammar= reassemble f' (subgrammar a)}
      where f' get set c = f (get . subgrammar) (\t->a{subgrammar= set t}) a{subgrammar= c}

boolean :: (BooleanDomain e, Functor1 g, Functor1 g') =>
           GrammarBuilder g g' String -> Production g (Parser g' String) e
        -> GrammarBuilder (Boolean g e) g' String
boolean sub start Boolean{..} = Boolean{
   expr= term
         <|> or <$> expr <* symbol "||" <*> term,
   term= factor
         <|> and <$> term <* symbol "&&" <*> factor,
   factor= keyword "True" *> pure true
           <|> keyword "False" *> pure false
           <|> keyword "not" *> takeCharsWhile isSpace *> (not <$> factor)
           <|> start subgrammar
           <|> symbol "(" *> expr <* symbol ")",
   subgrammar= sub subgrammar}
