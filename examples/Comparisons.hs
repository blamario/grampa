{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RecordWildCards, ScopedTypeVariables #-}
module Comparisons where

import Control.Applicative
import Data.Monoid ((<>))

import Text.Grampa
import Utilities (symbol)

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

infixJoin rel a b = a <> rel <> b

data Comparisons c e f =
   Comparisons{expr :: f e}

instance (Show (f c), Show (f e)) => Show (Comparisons c e f) where
   showsPrec prec g rest = "Comparisons{expr=" ++ showsPrec prec (expr g) ("}" ++ rest)

instance Functor1 (Comparisons c e) where
   fmap1 f g = g{expr= f (expr g)}

instance Apply1 (Comparisons c e) where
   ap1 a a' = Comparisons (expr a `apply1` expr a')

instance Alternative1 (Comparisons c e) where
   empty1 = Comparisons empty
   choose1 a a' = Comparisons{expr = expr a <|> expr a'}

instance Foldable1 (Comparisons c e) where
   foldMap1 f a = f (expr a)

instance Traversable1 (Comparisons c e) where
   traverse1 f a = Comparisons <$> f (expr a)

instance Reassemblable (Comparisons c e) where
   reassemble f a = Comparisons{expr= f expr a}

comparisons :: (ComparisonDomain c e, Functor1 g) => Parser g String c -> GrammarBuilder (Comparisons c e) g String
comparisons comparable Comparisons{..} =
   Comparisons{
      expr= lessThan <$> comparable <* symbol "<" <*> comparable
            <|> lessOrEqual <$> comparable <* symbol "<=" <*> comparable
            <|> equal <$> comparable <* symbol "==" <*> comparable
            <|> greaterOrEqual <$> comparable <* symbol ">=" <*> comparable
            <|> greaterThan <$> comparable <* symbol ">" <*> comparable}
