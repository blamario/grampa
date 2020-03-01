{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, RankNTypes, RecordWildCards,
             StandaloneDeriving, UndecidableInstances #-}
module Main where

import Control.Applicative ((<|>), empty)
import Control.Arrow (first)
import Control.Monad (guard, join)
import Data.Char (isSpace)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import System.Environment (getArgs)
import Text.Parser.Token (TokenParsing(..), symbol)
import qualified Text.Grampa
import Text.Grampa (TokenParsing(someSpace), LexicalParsing(lexicalComment, lexicalWhiteSpace, someLexicalSpace),
                    GrammarBuilder, ParseResults,
                    fixGrammar, parseComplete,
                    char, identifier, keyword, takeCharsWhile)
import Text.Grampa.ContextFree.SortedMemoizing.Transformer (ParserT, lift, tmap)
import qualified Boolean
import Boolean(Boolean(..))

type Parser = ParserT NodeWrap

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

type NodeWrap = (,) [[Either WhiteSpace Comment]]
newtype Comment    = Comment String    deriving Show
newtype WhiteSpace = WhiteSpace String deriving Show

type Grammar = Boolean.Boolean (NodeWrap (AST NodeWrap))

main :: IO ()
main = do args <- concat <$> getArgs
          let tree = (getCompose . fmap join . getCompose . Boolean.expr $
                      parseComplete (fixGrammar grammar) args :: ParseResults String [NodeWrap (AST NodeWrap)])
          print tree
          case tree
             of Right results -> mapM_ (print . reconstructed 0) results
                _ -> pure ()

reconstructed :: Int -> NodeWrap (AST NodeWrap) -> String
reconstructed prec (ws, node) = serialized prec ws node

serialized :: Int -> [[Either WhiteSpace Comment]] -> AST NodeWrap -> String
serialized prec [follow] (Or left right) | prec < 1 = reconstructed 1 left <> "||" <> whiteString follow <> reconstructed 0 right
serialized prec [follow] (And left right) | prec < 2 = reconstructed 2 left <> "&&" <> whiteString follow <> reconstructed 1 right
serialized prec [follow] (Not expr) | prec < 3 = "not" <> whiteString follow <> reconstructed 2 expr
serialized _ [follow] (Literal True) = "True" <> whiteString follow
serialized _ [follow] (Literal False) = "False" <> whiteString follow
serialized _ [follow] (Variable name) = name <> whiteString follow
serialized _ (precede:rest) node = "(" <> whiteString precede <> serialized 0 (init rest) node <> ")" <> whiteString (last rest)

whiteString :: [Either WhiteSpace Comment] -> String
whiteString (Left (WhiteSpace ws) : rest) = ws <> whiteString rest
whiteString (Right (Comment c) : rest) = "[" <> c <> "]" <> whiteString rest
whiteString [] = ""

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

storeWhiteSpace ([ws], (ws', a)) = ([], (ws' <> [ws], a))
storeWhiteSpace (ws:wss, (ws', a)) = ([], (ws : ws' <> wss, a))

instance {-# OVERLAPS #-} TokenParsing (Parser Grammar String) where
   someSpace = someLexicalSpace
   token p = p <* lexicalWhiteSpace

instance {-# OVERLAPS #-} LexicalParsing (Parser Grammar String) where
   lexicalWhiteSpace = tmap (first (\ws-> [concat ws])) $
                       do ws <- takeCharsWhile isSpace
                          lift ([[Left $ WhiteSpace ws]], ())
                          (lexicalComment *> lexicalWhiteSpace <|> pure ())
   lexicalComment = do char '['
                       comment <- takeCharsWhile (/= ']')
                       char ']'
                       lift ([[Right $ Comment comment]], ())
   identifierToken p = do ident <- p
                          guard (ident /= "True" && ident /= "False")
                          lexicalWhiteSpace
                          pure ident
