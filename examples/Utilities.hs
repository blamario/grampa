{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables #-}
module Utilities where

import Control.Applicative
import Data.Char (isAlphaNum, isSpace)

import Text.Grampa

keyword :: (Show s, TextualMonoid s, Functor1 g) => s -> Parser g s s
keyword kwd = skipCharsWhile isSpace *> string kwd <* notFollowedBy (satisfyChar isAlphaNum)

symbol :: (Show s, TextualMonoid s, Functor1 g) => s -> Parser g s s
symbol s = skipCharsWhile isSpace *> string s
