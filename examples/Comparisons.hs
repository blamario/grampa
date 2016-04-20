{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RecordWildCards, ScopedTypeVariables #-}
module Comparisons where

import Control.Applicative
import Control.Arrow (second)
import qualified Data.Bool 
import Data.Char (isSpace)
import Data.Monoid (Monoid, mappend, mempty, (<>))
import System.Environment (getArgs)

import Text.Grampa

import Prelude hiding (and, or, not)

class ComparisonDomain c e where
   greaterThan :: c -> c -> e
   lessThan :: c -> c -> e
   equal :: c -> c -> e
   greaterOrEqual :: c -> c -> e
   lessOrEqual :: c -> c -> e

instance Ord c => ComparisonDomain c Bool where
   greaterThan a b = a > b
   lessThan a b = a < b
   equal a b = a == b
   greaterOrEqual a b = a >= b
   lessOrEqual a b = a <= b

instance ComparisonDomain [Char] [Char] where
   lessThan = infixJoin "<"
   lessOrEqual = infixJoin "<="
   equal = infixJoin "=="
   greaterOrEqual = infixJoin ">="
   greaterThan = infixJoin ">"

infixJoin op a b = "(" <> a <> op <> b <> ")"

data Comparisons g e f =
   Comparisons{
      expr :: f e,
      comparable :: g f}

instance (Show (f e), Show (g f)) => Show (Comparisons g e f) where
   showsPrec prec a rest = "Comparisons{expr=" ++ showsPrec prec (expr a)
                           (", comparable=" ++ showsPrec prec (comparable a) ("}" ++ rest))

instance Functor1 g => Functor1 (Comparisons g e) where
   fmap1 f a = a{expr= f (expr a),
                 comparable= fmap1 f (comparable a)}

instance Foldable1 g => Foldable1 (Comparisons g e) where
   foldMap1 f a = f (expr a) <> foldMap1 f (comparable a)

instance Traversable1 g => Traversable1 (Comparisons g e) where
   traverse1 f a = Comparisons
                   <$> f (expr a)
                   <*> traverse1 f (comparable a)

instance Reassemblable g => Reassemblable (Comparisons g e) where
   composePer f g a = Comparisons{expr= expr (f a{expr= expr a'}),
                                  comparable= composePer f' g' (comparable a)}
      where a' = g a
            f' c = comparable (f $ a{comparable= c})
            g' c = comparable (g $ a{comparable= c})
   reassemble f a = Comparisons{expr= f expr a,
                                comparable= reassemble f' (comparable a)}
      where f' get c = f (get . comparable) a{comparable= c}
   reassemble' f a = Comparisons{expr= f expr (\e->a{expr= e}) a,
                                 comparable= reassemble' f' (comparable a)}
      where f' get set c = f (get . comparable) (\t->a{comparable= set t}) a{comparable= c}

comparisons :: (ComparisonDomain c e, Functor1 g, Functor1 g') =>
               Production g (Parser g' String) c -> GrammarBuilder g g' String -> GrammarBuilder (Comparisons g e) g' String
comparisons start subgrammar Comparisons{..} =
   let comparable' = start comparable
   in Comparisons{
            expr= lessThan <$> comparable' <* string "<" <*> comparable'
                  <|> lessOrEqual <$> comparable' <* string "<=" <*> comparable'
                  <|> equal <$> comparable' <* string "==" <*> comparable'
                  <|> greaterOrEqual <$> comparable' <* string ">=" <*> comparable'
                  <|> greaterThan <$> comparable' <* string ">" <*> comparable',
            comparable= subgrammar comparable}

parenthesize :: Reassemblable g =>
                (g (Parser (Comparisons g String) String) -> Parser (Comparisons g String) String String)
             -> (g (Parser (Comparisons g String) String) -> g (Parser (Comparisons g String) String))
             -> [String] -> [String]
parenthesize start subgrammar = parse (comparisons start subgrammar) expr

evaluate :: (Ord c, Reassemblable g) =>
            (g (Parser (Comparisons g Bool) String) -> Parser (Comparisons g Bool) String c)
         -> (g (Parser (Comparisons g Bool) String) -> g (Parser (Comparisons g Bool) String))
         -> [String] -> [Bool]
evaluate start subgrammar = parse (comparisons start subgrammar) expr

main start subgrammar = getArgs >>= print . evaluate start subgrammar
