{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, RecordWildCards, ScopedTypeVariables,
             TemplateHaskell, TypeFamilies, TypeOperators, UndecidableInstances #-}
module Boolean where

import Control.Applicative
import qualified Data.Bool
import Data.Char (isSpace)
import Data.Kind (Type)
import Data.Monoid ((<>))
import Text.Parser.Token (TokenParsing, symbol)

import qualified Rank2.TH

import Text.Grampa
import Utilities (infixJoin)

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

instance CharParsing (p (Boolean e) String) => TokenParsing (p (Boolean e) String)

instance (DeterministicParsing (p (Boolean e) String),
          InputCharParsing (p (Boolean e) String), ParserInput (p (Boolean e) String) ~ String) =>
         LexicalParsing (p (Boolean e) String)

$(Rank2.TH.deriveAll ''Boolean)

boolean :: forall e p (g :: (Type -> Type) -> Type).
           (BooleanDomain e, LexicalParsing (p g String), ParserInput (p g String) ~ String) =>
           p g String e -> Boolean e (p g String) -> Boolean e (p g String)
boolean p Boolean{..} = Boolean{
   expr= term
         <|> or <$> term <* symbol "||" <*> expr,
   term= factor
         <|> and <$> factor <* symbol "&&" <*> term,
   factor= keyword "True" *> pure true
           <|> keyword "False" *> pure false
           <|> keyword "not" *> takeCharsWhile isSpace *> (not <$> factor)
           <|> p
           <|> symbol "(" *> expr <* symbol ")"}
