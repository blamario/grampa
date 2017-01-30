{-# LANGUAGE KindSignatures, FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}
module Utilities where

import Control.Applicative (Alternative)
import Data.Char (isAlphaNum)
import Data.Monoid ((<>))

import Text.Grampa

infixJoin :: String -> String -> String -> String
infixJoin op a b = "(" <> a <> op <> b <> ")"

keyword :: forall s (g :: (* -> *) -> *) p. (Show s, TextualMonoid s, Parsing (p g s), MonoidParsing (p g)) => s -> p g s s
keyword kwd = whiteSpace *> string kwd <* notFollowedBy (satisfyChar isAlphaNum)

symbol :: forall s (g :: (* -> *) -> *) p. (Show s, TextualMonoid s, Applicative (p g s), MonoidParsing (p g)) => s -> p g s s
symbol s = whiteSpace *> string s
