{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, RecordWildCards, ScopedTypeVariables, TemplateHaskell #-}
module Boolean where

import Control.Applicative
import qualified Data.Bool
import Data.Char (isSpace)
import Data.Monoid ((<>))

import qualified Rank2.TH

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
   deriving Show

$(Rank2.TH.deriveAll ''Boolean)

boolean :: forall e p (g :: (* -> *) -> *).
           (BooleanDomain e, Alternative (p g String), Parsing (p g String), MonoidParsing (p g)) =>
           p g String e -> Boolean e (p g String) -> Boolean e (p g String)
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
