{-# LANGUAGE FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}
module Utilities where

import Data.Char (isAlphaNum)
import Data.Monoid ((<>))

import qualified Rank2
import Text.Grampa

infixJoin :: String -> String -> String -> String
infixJoin op a b = "(" <> a <> op <> b <> ")"

keyword :: (Show s, TextualMonoid s) => s -> Parser g s s
keyword kwd = spaces *> string kwd <* notFollowedBy (satisfyChar isAlphaNum)

symbol :: (Show s, TextualMonoid s) => s -> Parser g s s
symbol s = spaces *> string s
