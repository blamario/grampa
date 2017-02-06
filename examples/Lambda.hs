{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecordWildCards, ScopedTypeVariables, TemplateHaskell #-}
module Lambda where

import Control.Applicative
import Data.Char (isSpace, isLetter)
import Data.Map (Map, insert, (!))
import Data.Monoid ((<>))

import qualified Rank2
import qualified Rank2.TH

import Text.Grampa
import Utilities (infixJoin, keyword, symbol)

class LambdaDomain e where
   apply :: e -> e -> e
   lambda :: String -> e -> e
   var :: String -> e

data LambdaInitial = ApplyI LambdaInitial LambdaInitial
                   | LambdaI String LambdaInitial
                   | VarI String
                   deriving Show

data LambdaDeBruin = ApplyB LambdaDeBruin LambdaDeBruin
                   | LambdaB LambdaDeBruin
                   | VarB Int
                   deriving Show

data LambdaPHOAS a = ApplyP (LambdaPHOAS a) (LambdaPHOAS a)
                   | LambdaP (a -> LambdaPHOAS a)
                   | VarP a

instance LambdaDomain (Map String a -> [a] -> a) where
   apply f arg env stack = f env (arg env [] : stack)
   lambda v body env (arg:stack) = body (insert v arg env) stack
   var v env _stack = env ! v

reduceNormallyI :: Map String a -> [a] -> LambdaInitial -> a
reduceNormallyI env stack (ApplyI f arg) = reduceNormallyI env (reduceNormallyI env stack arg : stack) f
reduceNormallyI env (arg:stack) (LambdaI v body) = reduceNormallyI (insert v arg env) stack body
reduceNormallyI env _stack (VarI v) = env ! v

reduceNormallyP :: (a -> LambdaPHOAS a) -> LambdaPHOAS a -> LambdaPHOAS a
reduceNormallyP use (ApplyP f arg) = case reduceNormallyP use f
                                     of LambdaP f' -> reduceNormallyP use (reduceNormallyP f' arg)
                                        x -> ApplyP x arg
reduceNormallyP use (VarP x) = use x
reduceNormallyP _ x@LambdaP{} = x

instance LambdaDomain LambdaInitial where
   apply = ApplyI
   lambda = LambdaI
   var = VarI

instance LambdaDomain (Map String a -> LambdaPHOAS a) where
   apply f arg env = ApplyP (f env) (arg env)
   lambda v body env = LambdaP (\x-> body $ insert v x env)
   var v env = VarP (env ! v)

instance LambdaDomain (Map String Int -> Int -> LambdaDeBruin) where
   apply f arg env depth = ApplyB (f env depth) (arg env depth)
   lambda v body env depth = LambdaB (body (insert v (succ depth) env) (succ depth))
   var v env depth = VarB (depth - env ! v)

{-
instance LambdaDomain (Map String e -> [e] -> e) where
   apply f arg env stack = f env (arg env stack : stack)
   lambda v body env (arg : stack) = body (insert v arg env) stack
   var v map = (map ! v) map
-}

instance LambdaDomain String where
   apply f arg = f ++ " " ++ arg
   lambda v body = "(\\" ++ v ++ ". " ++ body ++ ")"
   var v = v

data Lambda e f =
   Lambda{
      expr :: f e,
      term :: f e,
      primary :: f e,
      varName :: f String}

$(Rank2.TH.deriveAll ''Lambda)

lambdaCalculus :: LambdaDomain e => GrammarBuilder (Lambda e) g String
lambdaCalculus Lambda{..} = Lambda{
   expr= lambda <$> (symbol "\\" *> varName <* symbol "->") <*> expr
         <|> term,
   term= apply <$> term <* takeCharsWhile1 isSpace <*> primary
         <|> primary,
   primary= var <$> varName
            <|> symbol "(" *> expr <* symbol ")",
   varName= takeCharsWhile1 isLetter}
