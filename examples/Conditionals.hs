{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RecordWildCards, ScopedTypeVariables #-}
module Conditionals where

import Control.Applicative
import Data.Monoid ((<>))

import qualified Rank2
import Text.Grampa
import Utilities (keyword)

class ConditionalDomain c e where
   ifThenElse :: c -> e -> e -> e

instance ConditionalDomain Bool e where
   ifThenElse True t _ = t
   ifThenElse False _ f = f

instance ConditionalDomain [Char] [Char] where
   ifThenElse cond t f = "if " <> cond <> " then " <> t <> " else " <> f

data Conditionals e f =
   Conditionals{
      expr :: f e}

instance Show (f e) => Show (Conditionals e f) where
   showsPrec prec a rest = "Conditionals{expr=" ++ showsPrec prec (expr a) ("}" ++ rest)

instance Rank2.Functor (Conditionals e) where
   fmap f a = a{expr= f (expr a)}

instance Rank2.Apply (Conditionals e) where
   ap a a' = Conditionals (expr a `Rank2.apply` expr a')

instance Rank2.Foldable (Conditionals e) where
   foldMap f a = f (expr a)

instance Rank2.Traversable (Conditionals e) where
   traverse f a = Conditionals <$> f (expr a)

instance Rank2.Reassemblable (Conditionals e) where
   reassemble f a = Conditionals{expr= f expr a}

conditionals :: (ConditionalDomain t e, Rank2.Functor g) =>
                Parser g String t -> Parser g String e -> GrammarBuilder (Conditionals e) g String
conditionals test term Conditionals{..} =
   Conditionals{expr= ifThenElse <$> (keyword "if" *> test) <*> (keyword "then" *> term) <*> (keyword "else" *> term)}
