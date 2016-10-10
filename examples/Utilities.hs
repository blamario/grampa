{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables #-}
module Utilities where

import Data.Char (isAlphaNum, isSpace)
import Data.Monoid ((<>))

import Text.Grampa

infixJoin :: String -> String -> String -> String
infixJoin op a b = "(" <> a <> op <> b <> ")"

keyword :: (Show s, TextualMonoid s, Functor1 g) => s -> Parser g s s
keyword kwd = skipCharsWhile isSpace *> string kwd <* notFollowedBy (satisfyChar isAlphaNum)

symbol :: (Show s, TextualMonoid s, Functor1 g) => s -> Parser g s s
symbol s = skipCharsWhile isSpace *> string s
