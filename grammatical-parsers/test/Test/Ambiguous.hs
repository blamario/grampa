{-# Language FlexibleInstances, RankNTypes, RecordWildCards, TemplateHaskell #-}
module Test.Ambiguous where

import Control.Applicative ((<|>), empty, liftA2)
import Data.Foldable (fold)
import Data.Semigroup ((<>))

import qualified Rank2.TH
import Text.Grampa
import Text.Grampa.Combinators
import Text.Grampa.ContextFree.SortedMemoizing.LeftRecursive (Parser)

import Debug.Trace

data Amb = Xy1 String String
         | Xy2 (Ambiguous Amb) String
         | Xyz (Ambiguous Amb) String
         | Xyzw (Ambiguous Amb) String
         deriving (Eq, Show)

data Test p = Test{
   amb :: p (Ambiguous Amb)
   }

$(Rank2.TH.deriveAll ''Test)

grammar :: Test (Parser Test String) -> Test (Parser Test String)
grammar Test{..} = Test{
   amb = ambiguous (Xy1 <$> string "x" <*> moptional (string "y")
                    <|> Xy2 <$> amb <*> string "y"
                    <|> Xyz <$> amb <*> string "z"
                    <|> Xyzw <$> amb <*> string "w")
   }
