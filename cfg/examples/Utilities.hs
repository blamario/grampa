{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, RankNTypes, ScopedTypeVariables #-}
module Utilities where

import Data.Char (isAlphaNum)
import Data.Functor.Compose (Compose(..))
import Data.List (intercalate)
import Data.Monoid ((<>))
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Monoid.Textual (TextualMonoid)

import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive
import qualified Rank2

parseUnique :: (FactorialMonoid s, Rank2.Traversable g, Rank2.Distributive g, Rank2.Apply g) =>
               Grammar g CompleteParser s -> (forall f. g f -> f r) -> s -> r
parseUnique g prod s = case getCompose (prod $ parse g s)
                       of Left (ParseFailure pos expected) -> error ("Parse failure at " ++ show pos
                                                                     ++ ", expected " ++ intercalate " or " expected)
                          Right [x] -> x

infixJoin :: String -> String -> String -> String
infixJoin op a b = "(" <> a <> op <> b <> ")"

keyword :: forall s (g :: (* -> *) -> *) p.
           (Show s, TextualMonoid s, Parsing (p g s), MonoidParsing (p g)) => s -> p g s s
keyword kwd = whiteSpace *> string kwd <* notFollowedBy (satisfyChar isAlphaNum)

symbol :: forall s (g :: (* -> *) -> *) p.
          (Show s, TextualMonoid s, Applicative (p g s), MonoidParsing (p g)) => s -> p g s s
symbol s = whiteSpace *> string s
