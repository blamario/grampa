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
   composePer f g a = Boolean{expr= expr (f a{expr= expr a'}),
                              term= term (f a{term= term a'}),
                              factor= factor (f a{factor= factor a'}),
                              subgrammar= composePer f' g' (subgrammar a)}
      where a' = g a
            f' c = subgrammar (f $ a{subgrammar= c})
            g' c = subgrammar (g $ a{subgrammar= c})
   reassemble f a = Boolean{expr= f expr a,
                            term= f term a,
                            factor= f factor a,
                            subgrammar= reassemble f' (subgrammar a)}
      where f' get c = f (get . subgrammar) a{subgrammar= c}
   reassemble' f a = Boolean{expr= f expr (\e->a{expr= e}) a,
                             term= f term (\t->a{term= t}) a,
                             factor= f factor (\f->a{factor= f}) a,
                             subgrammar= reassemble' f' (subgrammar a)}
      where f' get set c = f (get . subgrammar) (\t->a{subgrammar= set t}) a{subgrammar= c}

boolean :: (BooleanDomain e, Functor1 g) =>
           Production g (Parser (Boolean g e) String) e
        -> GrammarBuilder g (Boolean g e) String
        -> GrammarBuilder (Boolean g e) (Boolean g e) String
boolean start sub Boolean{..} = Boolean{
   expr= term
         <|> or <$> expr <* string "||" <*> term,
   term= factor
         <|> and <$> term <* string "&&" <*> factor,
   factor= string "True" *> pure true
           <|> string "False" *> pure false
           <|> string "not" *> takeCharsWhile isSpace *> (not <$> factor)
           <|> start subgrammar
           <|> string "(" *> expr <* string ")",
   subgrammar= sub subgrammar}

parenthesize :: Reassemblable g =>
                (g (Parser (Boolean g String) String) -> Parser (Boolean g String) String String)
             -> (g (Parser (Boolean g String) String) -> g (Parser (Boolean g String) String))
             -> [String] -> [String]
parenthesize start sub = parse (boolean start sub) expr

evaluate :: Reassemblable g =>
            (g (Parser (Boolean g Bool) String) -> Parser (Boolean g Bool) String Bool)
         -> (g (Parser (Boolean g Bool) String) -> g (Parser (Boolean g Bool) String))
         -> [String] -> [Bool]
evaluate start sub = parse (boolean start sub) expr

main start sub = getArgs >>= print . evaluate start sub
