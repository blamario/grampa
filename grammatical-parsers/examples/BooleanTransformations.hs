{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, RankNTypes, StandaloneDeriving, UndecidableInstances #-}
module Main where

import Control.Applicative (empty)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import System.Environment (getArgs)
import Text.Grampa (TokenParsing, LexicalParsing, GrammarBuilder, ParseResults, fixGrammar, parseComplete)
import Text.Grampa.ContextFree.SortedMemoizing.Transformer (ParserT)
import qualified Boolean

type Parser = ParserT Identity

data AST f = And (f (AST f)) (f (AST f))
           | Or (f (AST f)) (f (AST f))
           | Not (f (AST f))
           | Literal Bool
           | Variable String

deriving instance Show (f (AST f)) => Show (AST f)

instance Boolean.BooleanDomain (AST Identity) where
   and = binary And
   or = binary Or
   not = Not . pure
   true = Literal True
   false = Literal False

binary :: Applicative f => (f (AST f) -> f (AST f) -> AST f) -> AST f -> AST f -> AST f
binary f a b = f (pure a) (pure b)

type Grammar = Boolean.Boolean (AST Identity)
           
main :: IO ()
main = do args <- concat <$> getArgs
          print (getCompose . getCompose . Boolean.expr $
                 parseComplete (fixGrammar grammar) args :: ParseResults String [Identity (AST Identity)])

grammar :: GrammarBuilder Grammar Grammar Parser String
grammar = Boolean.boolean empty
