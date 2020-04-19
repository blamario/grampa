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
import Data.Maybe (mapMaybe)
import System.Environment (getArgs)
import Text.Parser.Token (TokenParsing(..), symbol)
import qualified Text.Grampa
import Text.Grampa (TokenParsing(someSpace), LexicalParsing(lexicalComment, lexicalWhiteSpace, someLexicalSpace),
                    GrammarBuilder, ParseResults,
                    fixGrammar, parseComplete,
                    char, identifier, keyword, takeCharsWhile)
import Text.Grampa.ContextFree.LeftRecursive.Transformer (ParserT, lift, tmap)
import qualified Boolean
import Boolean(Boolean(..))

-- |
-- >>> simplifiedSource "True && [comment] x"
-- "[comment] x"
-- >>> simplifiedSource "False || [comment1] (True || [comment2] x)"
-- "[comment1] True "
-- >>> simplifiedSource "False || [^ trailing comment] [leading comment] (True || [comment2] x)"
-- "[leading comment] True "
-- >>> simplifiedSource "False || [^ trailing comment] [leading comment] (True [operator leading] || [comment2] x)"
-- "[leading comment] True "
-- >>> simplifiedSource "([^1][1] True [^2][2] && [^3][3] x [^4][4])[^5][5] || [^6][6] False [^7][7]"
-- "[3] x [^4][^5]"

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
data AttachedIgnorables = Attached Ignorables AttachedIgnorables Ignorables
                        | Blank
                        | AttachedToOperator Ignorables Ignorables
                        | Parenthesized Ignorables AttachedIgnorables Ignorables
                        deriving Show
data ParsedIgnorables = Trailing Ignorables
                      | OperatorTrailing [Ignorables]
                      | ParenthesesTrailing Ignorables ParsedIgnorables Ignorables
                      deriving Show
type Ignorables = [Either WhiteSpace Comment]
newtype Comment    = Comment{getComment :: String} deriving Show
newtype WhiteSpace = WhiteSpace String deriving Show

type Grammar = Boolean.Boolean (ParsedWrap (AST ParsedWrap))

main :: IO ()
main = do args <- concat <$> getArgs
          let tree = parse args
          print tree
          case tree
             of Right [parsed] -> do let rearranged = completeRearranged mempty parsed
                                     print rearranged
                                     putStrLn (showSource $ simplified rearranged)
                other -> error (show other)

parse :: String -> ParseResults String [ParsedWrap (AST ParsedWrap)]
parse = getCompose . fmap snd . getCompose . Boolean.expr . parseComplete (fixGrammar grammar)

simplifiedSource :: String -> String
simplifiedSource input = case (parse input)
                         of Right [parsed] -> showSource (simplified $ completeRearranged mempty parsed)
                            other -> error (show other)

class ShowSource a where
   showSource :: a -> String
   showsSourcePrec :: Int -> a -> String -> String
   showSource a = showsSourcePrec 0 a mempty

instance ShowSource (NodeWrap (AST NodeWrap)) where
   showsSourcePrec prec (Attached lead Blank follow, node) rest =
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
completeRearranged ws node
   | ((ws', node'), trailing) <- rearranged ws node = (embed [] ws' trailing, node')

rearranged :: Ignorables -> ParsedWrap (AST ParsedWrap) -> (NodeWrap (AST NodeWrap), Ignorables)
rearranged leftover (Trailing follow, node)
   | (follow', lead') <- splitDirections follow, (lead'', node', follow'') <- rearrangedChildren [] node =
        ((Attached (leftover <> lead'') Blank (follow'' <> follow'), node'), lead')
rearranged leftover (OperatorTrailing [[], follow], node)
   | (follow', lead') <- splitDirections follow,
     (lead'', node', follow'') <- rearrangedChildren [[], lead'] node =
        ((Attached leftover (AttachedToOperator lead'' follow') [], node'), follow'')
rearranged leftover (ParenthesesTrailing lead ws follow, node)
   | (follow', lead') <- splitDirections follow, (ws', node') <- completeRearranged lead (ws, node) =
        ((Parenthesized leftover ws' follow', node'), lead')

embed leading Blank trailing = Attached leading Blank trailing
embed leading (Attached lead inside follow) trailing = embed (leading <> lead) inside (follow <> trailing)
embed leading (AttachedToOperator lead follow) trailing = AttachedToOperator (leading <> lead) (follow <> trailing)
embed leading (Parenthesized lead inside follow) trailing = Parenthesized (leading <> lead) inside (follow <> trailing)

rearrangedChildren :: [Ignorables] -> AST ParsedWrap -> (Ignorables, AST NodeWrap, Ignorables)
rearrangedChildren [left, right] (And a b)
   | (a', follow1) <- rearranged left a,
     (b', follow2) <- rearranged right b = (follow1, And a' b', follow2)
rearrangedChildren [left, right] (Or a b)
   | (a', follow1) <- rearranged left a,
     (b', follow2) <- rearranged right b = (follow1, Or a' b', follow2)
rearrangedChildren [leftover] (Not a)
   | (a', follow) <- rearranged leftover a = ([], Not a', follow)
rearrangedChildren [] (Literal a) = ([], Literal a, [])
rearrangedChildren [] (Variable name) = ([], Variable name, [])

-- | Separates the whitespace and comments that refer to the preceding construct.
splitDirections :: Ignorables -> (Ignorables, Ignorables)
splitDirections = span (either (const True) (isPrefixOf "^" . getComment))

-- | Simplifies the given expression according to the laws of Boolean algebra.
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
raise Blank arg = arg
raise op Blank = op
raise AttachedToOperator{} arg = arg
raise (Parenthesized opl op opr) arg = Parenthesized opl (raise op arg) opr
raise (Attached opl inside opr) (Parenthesized l arg r) =
   Parenthesized (comments opl <> l) (raise inside arg) (r <> comments opr)
raise (AttachedToOperator opl opr) (Parenthesized l arg r) = Parenthesized (comments opl <> l) arg (r <> comments opr)
raise (AttachedToOperator opl opr) (Attached argl inside argr) =
   Attached (comments opl <> argl) inside (argr <> comments opr)

comments :: Ignorables -> Ignorables
comments = mapMaybe (either (const Nothing) (Just . Right))

whiteString :: Ignorables -> String
whiteString (Left (WhiteSpace ws) : rest) = ws <> whiteString rest
whiteString (Right (Comment c) : rest) = "[" <> c <> "]" <> whiteString rest
whiteString [] = ""

grammar :: GrammarBuilder Grammar Grammar Parser String
grammar Boolean{..} = Boolean{
   expr= term
         <|> operatorTrailingWhiteSpace [mempty] (Boolean.or <$> term <* symbol "||" <*> expr),
   term= factor
         <|> operatorTrailingWhiteSpace [mempty] (Boolean.and <$> factor <* symbol "&&" <*> term),
   factor= trailingWhiteSpace (keyword "True" *> pure Boolean.true
                                 <|> keyword "False" *> pure Boolean.false
                                 <|> bare . Variable <$> identifier)
           <|> operatorTrailingWhiteSpace [] (keyword "not" *> (Boolean.not <$> factor))
           <|> parenthesizedWhiteSpace (symbol "(" *> expr <* symbol ")")}

bare :: a -> ParsedWrap a
bare a = (Trailing [], a)

operatorTrailingWhiteSpace :: [Ignorables] -> Parser Grammar String (ParsedWrap (AST ParsedWrap))
                           -> Parser Grammar String (ParsedWrap (AST ParsedWrap))
trailingWhiteSpace, parenthesizedWhiteSpace
   :: Parser Grammar String (ParsedWrap (AST ParsedWrap)) -> Parser Grammar String (ParsedWrap (AST ParsedWrap))
trailingWhiteSpace = tmap store
   where store ([ws], (Trailing ws', a)) = (mempty, (Trailing $ ws' <> ws, a))
operatorTrailingWhiteSpace prefix = tmap store
   where store (wss, (Trailing [], a)) = (mempty, (OperatorTrailing (prefix <> wss), a))
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
