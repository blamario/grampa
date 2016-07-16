{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RecordWildCards, ScopedTypeVariables #-}
module Conditionals where

import Control.Applicative
import Data.Monoid ((<>))

import Text.Grampa
import Utilities (keyword)

class ConditionalDomain c e where
   ifThenElse :: c -> e -> e -> e

instance ConditionalDomain Bool e where
   ifThenElse True t _ = t
   ifThenElse False _ f = f

instance ConditionalDomain [Char] [Char] where
   ifThenElse cond t f = "(if " <> cond <> " then " <> t <> " else " <> f <> ")"

data Conditionals e f =
   Conditionals{
      expr :: f e}

instance Show (f e) => Show (Conditionals e f) where
   showsPrec prec a rest = "Conditionals{expr=" ++ showsPrec prec (expr a) ("}" ++ rest)

instance Functor1 (Conditionals e) where
   fmap1 f a = a{expr= f (expr a)}

instance Apply1 (Conditionals e) where
   ap1 a a' = Conditionals (expr a `apply1` expr a')

instance Alternative1 (Conditionals e) where
   empty1 = Conditionals empty
   choose1 a a' = Conditionals{expr = expr a <|> expr a'}

instance Foldable1 (Conditionals e) where
   foldMap1 f a = f (expr a)

instance Traversable1 (Conditionals e) where
   traverse1 f a = Conditionals <$> f (expr a)

instance Reassemblable (Conditionals e) where
   applyFieldwise f a b = Conditionals{expr= expr (f b{expr= expr a})}
   reassemble f a = Conditionals{expr= f expr (\e->a{expr= e}) a}

conditionals :: (ConditionalDomain t e, Functor1 g) =>
                Parser g String t -> Parser g String e -> GrammarBuilder (Conditionals e) g String
conditionals test term Conditionals{..} =
   Conditionals{expr= ifThenElse <$> (keyword "if" *> test) <*> (keyword "then" *> term) <*> (keyword "else" *> term)}
