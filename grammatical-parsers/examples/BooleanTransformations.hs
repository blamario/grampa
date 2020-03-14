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

type Parser = ParserT ((,) [Ignorables])

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

type NodeWrap = (,) AttachedIgnorables
data AttachedIgnorables = Trailing Ignorables
                        | Parenthesized Ignorables AttachedIgnorables Ignorables deriving Show
type Ignorables = [Either WhiteSpace Comment]
newtype Comment    = Comment String    deriving Show
newtype WhiteSpace = WhiteSpace String deriving Show

type Grammar = Boolean.Boolean (NodeWrap (AST NodeWrap))

instance Semigroup AttachedIgnorables where
   Trailing a <> Trailing b = Trailing (a <> b)
   Parenthesized a b c <> Trailing d = Parenthesized a b (c <> d)
   Trailing a <> Parenthesized b c d = Parenthesized (a <> b) c d
   a <> b = error (show (a, b))
instance Monoid AttachedIgnorables where
   mempty = Trailing mempty

main :: IO ()
main = do args <- concat <$> getArgs
          let tree = (getCompose . fmap snd . getCompose . Boolean.expr $
                      parseComplete (fixGrammar grammar) args :: ParseResults String [NodeWrap (AST NodeWrap)])
          print tree
          case tree
             of Right results -> do mapM_ (print . reconstructed 0) results
                                    mapM_ (print . reconstructed 0 . simplified) results
                _ -> pure ()

reconstructed :: Int -> NodeWrap (AST NodeWrap) -> String
reconstructed prec (ws, node) = serialized prec ws node

simplified :: Monoid a => (a, AST ((,) a)) -> (a, AST ((,) a))
simplified e@(_, Literal{}) = e
simplified e@(_, Variable{}) = e
simplified (a, Not e) = case simplified e
                        of (b, Literal True) -> (a <> b, Literal False)
                           (b, Literal False) -> (a <> b, Literal True)
                           e' -> (a, Not e')
simplified (a, And l r) = case (simplified l, simplified r)
                          of ((b, Literal False), _) -> (a <> b, Literal False)
                             ((b, Literal True), (c, r')) -> (a <> b <> c, r')
                             (_, (b, Literal False)) -> (a <> b, Literal False)
                             ((b, l'), (c, Literal True)) -> (a <> b <> c, l')
                             (l', r') -> (a, And l' r')
simplified (a, Or l r) =  case (simplified l, simplified r)
                          of ((b, Literal False), (c, r')) -> (a <> b <> c, r')
                             ((b, Literal True), _) -> (a <> b, Literal True)
                             ((b, l'), (c, Literal False)) -> (a <> b <> c, l')
                             (_, (b, Literal True)) -> (a <> b, Literal True)
                             (l', r') -> (a, Or l' r')

serialized :: Int -> AttachedIgnorables -> AST NodeWrap -> String
serialized prec (Trailing follow) (Or left right)
   | prec < 1 = reconstructed 1 left <> "||" <> whiteString follow <> reconstructed 0 right
serialized prec (Trailing follow) (And left right)
   | prec < 2 = reconstructed 2 left <> "&&" <> whiteString follow <> reconstructed 1 right
serialized prec (Trailing follow) (Not expr) | prec < 3 = "not" <> whiteString follow <> reconstructed 2 expr
serialized _ (Trailing follow) (Literal True) = "True" <> whiteString follow
serialized _ (Trailing follow) (Literal False) = "False" <> whiteString follow
serialized _ (Trailing follow) (Variable name) = name <> whiteString follow
serialized _ (Parenthesized open inside close) node =
   "(" <> whiteString open <> serialized 0 inside node <> ")" <> whiteString close

whiteString :: Ignorables -> String
whiteString (Left (WhiteSpace ws) : rest) = ws <> whiteString rest
whiteString (Right (Comment c) : rest) = "[" <> c <> "]" <> whiteString rest
whiteString [] = ""

grammar :: GrammarBuilder Grammar Grammar Parser String
grammar Boolean{..} = Boolean{
   expr= term
         <|> trailingWhiteSpace (Boolean.or <$> term <* symbol "||" <*> expr),
   term= factor
         <|> trailingWhiteSpace (Boolean.and <$> factor <* symbol "&&" <*> term),
   factor= trailingWhiteSpace (keyword "True" *> pure Boolean.true
                                 <|> keyword "False" *> pure Boolean.false
                                 <|> pure . Variable <$> identifier
                                 <|> keyword "not" *> (Boolean.not <$> factor))
           <|> parenthesizedWhiteSpace (symbol "(" *> expr <* symbol ")")}

trailingWhiteSpace, parenthesizedWhiteSpace :: Parser Grammar String (NodeWrap (AST NodeWrap))
                                            -> Parser Grammar String (NodeWrap (AST NodeWrap))
trailingWhiteSpace = tmap store
   where store ([ws], (Trailing ws', a)) = (mempty, (Trailing $ ws' <> ws, a))
parenthesizedWhiteSpace = tmap store
   where store ([ws,ws'], (aws, a)) = ([], (Parenthesized ws aws ws', a))

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
