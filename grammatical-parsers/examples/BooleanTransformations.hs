{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, RankNTypes, RecordWildCards,
             StandaloneDeriving, UndecidableInstances #-}
module Main where

import Control.Applicative ((<|>), empty)
import Control.Monad (guard)
import Data.Char (isSpace)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import System.Environment (getArgs)
import Text.Parser.Token (TokenParsing(..), symbol)
import qualified Text.Grampa
import Text.Grampa (TokenParsing(someSpace), LexicalParsing(lexicalWhiteSpace, someLexicalSpace), GrammarBuilder, ParseResults,
                    fixGrammar, parseComplete,
                    identifier, keyword, takeCharsWhile)
import Text.Grampa.ContextFree.SortedMemoizing.Transformer (ParserT, lift, tmap)
import qualified Boolean
import Boolean(Boolean(..))

type Parser = ParserT ((,) [String])

data AST f = And (f (AST f)) (f (AST f))
           | Or (f (AST f)) (f (AST f))
           | Not (f (AST f))
           | Literal Bool
           | Variable String

deriving instance (Show (f (AST f)), Show (f Bool), Show (f String)) => Show (AST f)

instance Boolean.BooleanDomain (NodeWrap (AST NodeWrap)) where
   and = binary And
   or = binary Or
   not = pure . Not
   true = pure (Literal True)
   false = pure (Literal False)

binary :: Applicative f => (f (AST f) -> f (AST f) -> AST f) -> f (AST f) -> f (AST f) -> f (AST f)
binary f a b = pure (f a b)

type NodeWrap = (,) [String]
type Grammar = Boolean.Boolean (NodeWrap (AST NodeWrap))

main :: IO ()
main = do args <- concat <$> getArgs
          let tree = (getCompose . getCompose . Boolean.expr $
                      parseComplete (fixGrammar grammar) args :: ParseResults String [([String], NodeWrap (AST NodeWrap))])
          print tree
          case tree
             of Right results -> mapM_ (putStrLn . reconstructed 0 . snd) results
                _ -> pure ()

reconstructed :: Int -> NodeWrap (AST NodeWrap) -> String
reconstructed prec (ws, node) = serialized prec ws node

serialized :: Int -> [String] -> AST NodeWrap -> String
serialized prec [follow] (Or left right) | prec < 1 = reconstructed 1 left <> "||" <> follow <> reconstructed 2 right
serialized prec [follow] (And left right) | prec < 2 = reconstructed 2 left <> "&&" <> follow <> reconstructed 1 right
serialized prec [follow] (Not expr) | prec < 3 = "not" <> follow <> reconstructed 2 expr
serialized _ [follow] (Literal True) = "True" <> follow
serialized _ [follow] (Literal False) = "False" <> follow
serialized _ [follow] (Variable name) = name <> follow
serialized _ (precede:rest) node = "(" <> precede <> serialized 0 (init rest) node <> ")" <> last rest

grammar :: GrammarBuilder Grammar Grammar Parser String
grammar Boolean{..} = Boolean{
   expr= term
         <|> tmap storeWhiteSpace (Boolean.or <$> term <* symbol "||" <*> expr),
   term= factor
         <|> tmap storeWhiteSpace (Boolean.and <$> factor <* symbol "&&" <*> term),
   factor= tmap storeWhiteSpace (keyword "True" *> pure Boolean.true
                                 <|> keyword "False" *> pure Boolean.false
                                 <|> pure . Variable <$> identifier
                                 <|> keyword "not" *> takeCharsWhile isSpace *> (Boolean.not <$> factor)
                                 <|> symbol "(" *> expr <* symbol ")")}

storeWhiteSpace (ws, (ws', a)) = ([], (ws <> ws', a))

instance {-# OVERLAPS #-} TokenParsing (Parser Grammar String) where
   someSpace = someLexicalSpace
   token p = p <* lexicalWhiteSpace

instance {-# OVERLAPS #-} LexicalParsing (Parser Grammar String) where
   lexicalWhiteSpace = do ws <- takeCharsWhile isSpace
                          lift ([ws], ())
   identifierToken p = do ident <- p
                          guard (ident /= "True" && ident /= "False")
                          lexicalWhiteSpace
                          pure ident
