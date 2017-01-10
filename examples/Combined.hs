{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}

module Combined where

import Control.Applicative
import qualified Data.Bool
import Data.Monoid ((<>))
import qualified Rank2
import Text.Grampa (GrammarBuilder)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons
import qualified Conditionals

data Expression f =
   Expression{
      expr :: f Tagged,
      arithmeticGrammar :: Arithmetic.Arithmetic Tagged f,
      booleanGrammar :: Boolean.Boolean Tagged f,
      comparisonGrammar :: Comparisons.Comparisons Tagged Bool f,
      conditionalGrammar :: Conditionals.Conditionals Tagged f}

data Tagged = IntExpression {intFromExpression :: Int}
            | BoolExpression {boolFromExpression :: Bool}
            deriving (Eq, Ord, Show)

instance Arithmetic.ArithmeticDomain Tagged where
   number = IntExpression
   IntExpression a `add` IntExpression b = IntExpression (a+b)
   _ `add` _ = error "type error: add expects numbers"
   IntExpression a `multiply` IntExpression b = IntExpression (a*b)
   _ `multiply` _ = error "type error: multiply expects numbers"
   negate (IntExpression a) = IntExpression (Prelude.negate a)
   negate _ = error "type error: negate expects a number"
   IntExpression a `subtract` IntExpression b = IntExpression (a-b)
   _ `subtract` _ = error "type error: subtract expects numbers"
   IntExpression a `divide` IntExpression b = IntExpression (div a b)
   _ `divide` _ = error "type error: divide expects numbers"

instance Boolean.BooleanDomain Tagged where
   true = BoolExpression True
   false = BoolExpression False
   BoolExpression x `and` BoolExpression y = BoolExpression (x && y)
   _ `and` _ = error "type error: and expects booleans"
   BoolExpression x `or` BoolExpression y = BoolExpression (x || y)
   _ `or` _ = error "type error: or expects booleans"
   not (BoolExpression x) = BoolExpression (Data.Bool.not x)
   not _ = error "type error: not expects a boolean"

instance Conditionals.ConditionalDomain Tagged e where
   ifThenElse (BoolExpression True) t _ = t
   ifThenElse (BoolExpression False) _ f = f
   ifThenElse _ _ _ = error "type error: if expects a boolean"

instance (Show (f Tagged), Show (f Int), Show (f Bool)) => Show (Expression f) where
   showsPrec prec g rest = "Expression{expr=" ++ showsPrec prec (expr g)
                           (", arithmeticGrammar=" ++ showsPrec prec (arithmeticGrammar g)
                           (", booleanGrammar=" ++ showsPrec prec (booleanGrammar g)
                           (", comparisonGrammar=" ++ showsPrec prec (comparisonGrammar g)
                           (", conditionalGrammar=" ++ showsPrec prec (conditionalGrammar g) ("}" ++ rest)))))

instance Rank2.Functor Expression where
   fmap f g = g{expr= f (expr g),
                arithmeticGrammar= Rank2.fmap f (arithmeticGrammar g),
                booleanGrammar= Rank2.fmap f (booleanGrammar g),
                comparisonGrammar= Rank2.fmap f (comparisonGrammar g),
                conditionalGrammar= Rank2.fmap f (conditionalGrammar g)}

instance Rank2.Apply Expression where
   ap a b = Expression{expr= expr a `Rank2.apply` expr b,
                       arithmeticGrammar= arithmeticGrammar a `Rank2.ap` arithmeticGrammar b,
                       booleanGrammar= booleanGrammar a `Rank2.ap` booleanGrammar b,
                       comparisonGrammar= comparisonGrammar a `Rank2.ap` comparisonGrammar b,
                       conditionalGrammar= conditionalGrammar a `Rank2.ap` conditionalGrammar b}

instance Rank2.Applicative Expression where
   pure f = Expression{expr= f,
                       arithmeticGrammar= Rank2.pure f,
                       booleanGrammar= Rank2.pure f,
                       comparisonGrammar= Rank2.pure f,
                       conditionalGrammar= Rank2.pure f}

instance Rank2.Distributive Expression where
   distributeM f = Expression{expr= f >>= expr,
                              arithmeticGrammar= Rank2.distributeM (arithmeticGrammar <$> f),
                              booleanGrammar= Rank2.distributeM (booleanGrammar <$> f),
                              comparisonGrammar= Rank2.distributeM (comparisonGrammar <$> f),
                              conditionalGrammar= Rank2.distributeM (conditionalGrammar <$> f)}
   distributeWith w f = Expression{expr= w (expr <$> f),
                                   arithmeticGrammar= Rank2.distributeWith w (arithmeticGrammar <$> f),
                                   booleanGrammar= Rank2.distributeWith w (booleanGrammar <$> f),
                                   comparisonGrammar= Rank2.distributeWith w (comparisonGrammar <$> f),
                                   conditionalGrammar= Rank2.distributeWith w (conditionalGrammar <$> f)}

instance Rank2.Foldable Expression where
   foldMap f g = f (expr g) <> Rank2.foldMap f (arithmeticGrammar g) <> Rank2.foldMap f (booleanGrammar g)
                 <> Rank2.foldMap f (comparisonGrammar g) <> Rank2.foldMap f (conditionalGrammar g)

instance Rank2.Traversable Expression where
   traverse f g = Expression
                  <$> f (expr g)
                  <*> Rank2.traverse f (arithmeticGrammar g)
                  <*> Rank2.traverse f (booleanGrammar g)
                  <*> Rank2.traverse f (comparisonGrammar g)
                  <*> Rank2.traverse f (conditionalGrammar g)

expression :: GrammarBuilder Expression g String
expression Expression{expr= expr,
                      arithmeticGrammar= arithmetic@Arithmetic.Arithmetic{Arithmetic.expr= arithmeticExpr},
                      booleanGrammar= boolean@Boolean.Boolean{Boolean.expr= booleanExpr},
                      comparisonGrammar= comparisons@Comparisons.Comparisons{Comparisons.test= comparisonTest},
                      conditionalGrammar= conditionals@Conditionals.Conditionals{Conditionals.expr= conditionalExpr}} =
   Expression{expr= arithmeticExpr
                    <|> booleanExpr
                    <|> conditionalExpr,
              arithmeticGrammar= Arithmetic.arithmetic conditionalExpr arithmetic,
              booleanGrammar= Boolean.boolean (BoolExpression <$> comparisonTest) boolean,
              comparisonGrammar= Comparisons.comparisons arithmeticExpr comparisons,
              conditionalGrammar= Conditionals.conditionals booleanExpr expr conditionals}
