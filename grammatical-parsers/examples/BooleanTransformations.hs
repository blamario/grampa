{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, RankNTypes, RecordWildCards,
             StandaloneDeriving, UndecidableInstances #-}
module Main where

import Control.Applicative ((<|>), empty)
import Control.Arrow (first)
import Control.Monad (guard, join)
import Data.Char (isSpace)
import Data.List (isPrefixOf)
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

instance Boolean.BooleanDomain (ParsedWrap (AST ParsedWrap)) where
   and = binary And
   or = binary Or
   not = bare . Not
   true = bare (Literal True)
   false = bare (Literal False)

binary :: (ParsedWrap (AST ParsedWrap) -> ParsedWrap (AST ParsedWrap) -> AST ParsedWrap)
       -> ParsedWrap (AST ParsedWrap) -> ParsedWrap (AST ParsedWrap) -> ParsedWrap (AST ParsedWrap)
binary f a b = bare (f a b)

type ParsedWrap = (,) ParsedIgnorables
type NodeWrap = (,) AttachedIgnorables
data AttachedIgnorables = Attached Ignorables Ignorables
                        | Parenthesized Ignorables AttachedIgnorables Ignorables
                        deriving Show
data ParsedIgnorables = Trailing Ignorables
                      | OperatorTrailing Ignorables
                      | ParenthesesTrailing Ignorables ParsedIgnorables Ignorables
                      deriving Show
type Ignorables = [Either WhiteSpace Comment]
newtype Comment    = Comment{getComment :: String} deriving Show
newtype WhiteSpace = WhiteSpace String deriving Show

type Grammar = Boolean.Boolean (ParsedWrap (AST ParsedWrap))

main :: IO ()
main = do args <- concat <$> getArgs
          let tree = (getCompose . fmap snd . getCompose . Boolean.expr $
                      parseComplete (fixGrammar grammar) args :: ParseResults String [ParsedWrap (AST ParsedWrap)])
          print tree
          case (completeRearranged mempty <$>) <$> tree
             of Right results -> do mapM_ (print . show) results
                                    mapM_ (print . showSource . simplified) results
                _ -> pure ()

class ShowSource a where
   showSource :: a -> String
   showsSourcePrec :: Int -> a -> String -> String
   showSource a = showsSourcePrec 0 a mempty

instance ShowSource (NodeWrap (AST NodeWrap)) where
   showsSourcePrec prec (Attached lead follow, node) rest =
      whiteString lead <> showsSourcePrec prec node (whiteString follow <> rest)
   showsSourcePrec prec (Parenthesized lead ws follow, node) rest =
      whiteString lead <> showsSourcePrec 0 (ws, node) (whiteString follow <> rest)

instance ShowSource (AST NodeWrap) where
   showsSourcePrec prec (Or left right) rest
      | prec < 1 = showsSourcePrec 1 left ("||" <> showsSourcePrec 0 right rest)
   showsSourcePrec prec (And left right) rest
      | prec < 2 = showsSourcePrec 2 left ("&&" <> showsSourcePrec 1 right rest)
   showsSourcePrec prec (Not expr) rest
      | prec < 3 = "not" <> showsSourcePrec 2 expr rest
   showsSourcePrec _ (Literal True) rest = "True" <> rest
   showsSourcePrec _ (Literal False) rest = "False" <> rest
   showsSourcePrec _ (Variable name) rest = name <> rest
   showsSourcePrec _ node rest =   "(" <> showsSourcePrec 0 node (")" <> rest)

completeRearranged :: Ignorables -> ParsedWrap (AST ParsedWrap) -> NodeWrap (AST NodeWrap)
completeRearranged ws node | ((ws', node'), rest) <- rearranged ws node = (withTail ws' rest, node')

rearranged :: Ignorables -> ParsedWrap (AST ParsedWrap) -> (NodeWrap (AST NodeWrap), Ignorables)
rearranged leftover (Trailing follow, node)
   | (follow', lead') <- splitDirections follow, (node', follow'') <- rearrangedChildren mempty mempty node =
        ((Attached leftover (follow'' <> follow'), node'), lead')
rearranged leftover (OperatorTrailing follow, node)
   | (node', follow') <- rearrangedChildren mempty follow node = ((Attached leftover mempty, node'), follow')
rearranged leftover (ParenthesesTrailing lead ws follow, node)
   | (follow', lead') <- splitDirections follow, ((ws', node'), follow'') <- rearranged lead (ws, node) =
        ((Parenthesized leftover (ws' `withTail` follow'') follow', node'), lead')

withTail (Attached lead follow) ws = Attached lead (follow <> ws)
withTail (Parenthesized lead inside follow) ws = Parenthesized lead inside (follow <> ws)

rearrangedChildren :: Ignorables -> Ignorables -> AST ParsedWrap -> (AST NodeWrap, Ignorables)
rearrangedChildren left right (And a b)
   | a' <- completeRearranged left a,
     (b', rest') <- rearranged right b = (And a' b', rest')
rearrangedChildren left right (Or a b)
   | a' <- completeRearranged left a,
     (b', rest') <- rearranged right b = (Or a' b', rest')
rearrangedChildren leftover [] (Not a)
   | (a', rest) <- rearranged leftover a = (Not a', rest)
rearrangedChildren [] [] (Literal a) = (Literal a, [])
rearrangedChildren [] [] (Variable name) = (Variable name, [])

splitDirections :: Ignorables -> (Ignorables, Ignorables)
splitDirections = span (either (const True) (isPrefixOf "^" . getComment))

simplified :: NodeWrap (AST NodeWrap) -> NodeWrap (AST NodeWrap)
simplified e@(_, Literal{}) = e
simplified e@(_, Variable{}) = e
simplified (a, Not e) = case simplified e
                        of (b, Literal True) -> (raise a b, Literal False)
                           (b, Literal False) -> (raise a b, Literal True)
                           e' -> (a, Not e')
simplified (a, And l r) = case (simplified l, simplified r)
                          of ((b, Literal False), _) -> (raise a b, Literal False)
                             ((b, Literal True), (c, r')) -> (raise a c, r')
                             (_, (b, Literal False)) -> (raise a b, Literal False)
                             ((b, l'), (c, Literal True)) -> (raise a b, l')
                             (l', r') -> (a, And l' r')
simplified (a, Or l r) =  case (simplified l, simplified r)
                          of ((b, Literal False), (c, r')) -> (raise a c, r')
                             ((b, Literal True), _) -> (raise a b, Literal True)
                             ((b, l'), (c, Literal False)) -> (raise a b, l')
                             (_, (b, Literal True)) -> (raise a b, Literal True)
                             (l', r') -> (a, Or l' r')

raise :: AttachedIgnorables -> AttachedIgnorables -> AttachedIgnorables
raise  (Parenthesized opl op opr) arg = Parenthesized opl (raise op arg) opr
raise  (Attached opl opr) (Parenthesized l arg r) = Parenthesized (opl <> l) arg (r <> opr)
raise  (Attached opl opr) (Attached argl argr) = Attached (opl <> argl) (argr <> opr)

whiteString :: Ignorables -> String
whiteString (Left (WhiteSpace ws) : rest) = ws <> whiteString rest
whiteString (Right (Comment c) : rest) = "[" <> c <> "]" <> whiteString rest
whiteString [] = ""

grammar :: GrammarBuilder Grammar Grammar Parser String
grammar Boolean{..} = Boolean{
   expr= term
         <|> operatorTrailingWhiteSpace (Boolean.or <$> term <* symbol "||" <*> expr),
   term= factor
         <|> operatorTrailingWhiteSpace (Boolean.and <$> factor <* symbol "&&" <*> term),
   factor= trailingWhiteSpace (keyword "True" *> pure Boolean.true
                                 <|> keyword "False" *> pure Boolean.false
                                 <|> bare . Variable <$> identifier
                                 <|> keyword "not" *> (Boolean.not <$> factor))
           <|> parenthesizedWhiteSpace (symbol "(" *> expr <* symbol ")")}

bare :: a -> ParsedWrap a
bare a = (Trailing [], a)

trailingWhiteSpace, operatorTrailingWhiteSpace, parenthesizedWhiteSpace
   :: Parser Grammar String (ParsedWrap (AST ParsedWrap)) -> Parser Grammar String (ParsedWrap (AST ParsedWrap))
trailingWhiteSpace = tmap store
   where store ([ws], (Trailing ws', a)) = (mempty, (Trailing $ ws' <> ws, a))
operatorTrailingWhiteSpace = tmap store
   where store ([ws], (Trailing [], a)) = (mempty, (OperatorTrailing ws, a))
parenthesizedWhiteSpace = tmap store
   where store ([ws,ws'], (aws, a)) = ([], (ParenthesesTrailing ws aws ws', a))

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
