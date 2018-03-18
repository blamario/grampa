{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables #-}
module Arithmetic where

import Control.Applicative
import Data.Char (isDigit)
import Data.Functor.Compose (Compose(..))
import Data.Monoid ((<>))

import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive (Parser)
import Utilities (infixJoin)

import qualified Rank2
import Prelude hiding (negate, product, subtract, sum)

class ArithmeticDomain e where
   number :: Int -> e
   add :: e -> e -> e
   multiply :: e -> e -> e
   negate :: e -> e
   subtract :: e -> e -> e
   divide :: e -> e -> e

instance ArithmeticDomain Int where
   number = id
   add = (+)
   multiply = (*)
   negate = (0 -)
   subtract = (-)
   divide = div

instance ArithmeticDomain [Char] where
   number = show
   add = infixJoin "+"
   multiply = infixJoin "*"
   negate = ("-" <>)
   subtract = infixJoin "-"
   divide = infixJoin "/"

data Arithmetic e f = Arithmetic{expr    :: f e,
                                 sum     :: f e,
                                 product :: f e,
                                 factor  :: f e,
                                 primary :: f e}

instance Show (f e) => Show (Arithmetic e f) where
   showsPrec prec a rest = "Arithmetic{expr=" ++ showsPrec prec (expr a)
                           (", sum=" ++ showsPrec prec (sum a)
                            (", product=" ++ showsPrec prec (product a)
                             (", factor=" ++ showsPrec prec (factor a)
                              (", primary=" ++ showsPrec prec (primary a) ("}" ++ rest)))))

instance Rank2.Functor (Arithmetic e) where
   f <$> a = a{expr= f (expr a),
               sum= f (sum a),
               product= f (product a),
               factor= f (factor a),
               primary= f (primary a)}

instance Rank2.Apply (Arithmetic e) where
   a <*> a' = Arithmetic (expr a `Rank2.apply` expr a')
                         (sum a `Rank2.apply` sum a')
                         (product a `Rank2.apply` product a')
                         (factor a `Rank2.apply` factor a')
                         (primary a `Rank2.apply` primary a')

instance Rank2.Applicative (Arithmetic e) where
   pure f = Arithmetic f f f f f

instance Rank2.DistributiveTraversable (Arithmetic e)

instance Rank2.Distributive (Arithmetic e) where
   cotraverse w f = Arithmetic{expr= w (expr <$> f),
                               sum= w (sum <$> f),
                               product= w (product <$> f),
                               factor= w (factor <$> f),
                               primary= w (primary <$> f)}

instance Rank2.Foldable (Arithmetic e) where
   foldMap f a = f (expr a) <> f (sum a) <> f (product a) <> f (factor a) <> f (primary a)

instance Rank2.Traversable (Arithmetic e) where
   traverse f a = Arithmetic
                  <$> f (expr a)
                  <*> f (sum a)
                  <*> f (product a)
                  <*> f (factor a)
                  <*> f (primary a)

instance Lexical (Arithmetic e)

arithmetic :: (Lexical g, LexicalConstraint Parser g String, ArithmeticDomain e) =>
              GrammarBuilder (Arithmetic e) g Parser String
arithmetic Arithmetic{..} = Arithmetic{
   expr= sum,
   sum= product
         <|> symbol "-" *> (negate <$> product)
         <|> add <$> sum <* symbol "+" <*> product
         <|> subtract <$> sum <* symbol "-" <*> product,
   product= factor
         <|> multiply <$> product <* symbol "*" <*> factor
         <|> divide <$> product <* symbol "/" <*> factor,
   factor= primary
           <|> symbol "(" *> expr <* symbol ")",
   primary= lexicalToken ((number . read) <$> takeCharsWhile1 isDigit) <?> "digits"}

main :: IO ()
main = getContents >>=
       print . (getCompose . expr . parseComplete (fixGrammar arithmetic) :: String -> ParseResults [Int])
