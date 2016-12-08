{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RecordWildCards, ScopedTypeVariables #-}
module Comparisons where

import Control.Applicative
import Data.Monoid ((<>))

import qualified Rank2
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

infixJoin :: String -> String -> String -> String
infixJoin rel a b = a <> rel <> b

data Comparisons c e f =
   Comparisons{expr :: f e}

instance (Show (f e)) => Show (Comparisons c e f) where
   showsPrec prec g rest = "Comparisons{expr=" ++ showsPrec prec (expr g) ("}" ++ rest)

instance Rank2.Functor (Comparisons c e) where
   fmap f g = g{expr= f (expr g)}

instance Rank2.Apply (Comparisons c e) where
   ap a a' = Comparisons (expr a `Rank2.apply` expr a')

instance Rank2.Applicative (Comparisons c e) where
   pure = Comparisons

instance Rank2.Foldable (Comparisons c e) where
   foldMap f a = f (expr a)

instance Rank2.Traversable (Comparisons c e) where
   traverse f a = Comparisons <$> f (expr a)

instance Rank2.Reassemblable (Comparisons c e) where
   reassemble f a = Comparisons{expr= f expr a}

comparisons :: (ComparisonDomain c e) => Parser g String c -> GrammarBuilder (Comparisons c e) g String
comparisons comparable Comparisons{..} =
   Comparisons{
      expr= lessThan <$> comparable <* symbol "<" <*> comparable
            <|> lessOrEqual <$> comparable <* symbol "<=" <*> comparable
            <|> equal <$> comparable <* symbol "==" <*> comparable
            <|> greaterOrEqual <$> comparable <* symbol ">=" <*> comparable
            <|> greaterThan <$> comparable <* symbol ">" <*> comparable}
