{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, RecordWildCards, UndecidableInstances #-}

module Combined where

import Control.Applicative
import qualified Data.Bool
import Data.Monoid ((<>))
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Rank2
import Text.Grampa (GrammarBuilder)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons
import qualified Conditionals
import qualified Lambda

data Expression f =
   Expression{
      expr :: f Domain,
      term :: f Domain,
      primary :: f Domain,
      arithmeticGrammar :: Arithmetic.Arithmetic Domain f,
      booleanGrammar :: Boolean.Boolean Domain f,
      comparisonGrammar :: Comparisons.Comparisons Domain Domain f,
      conditionalGrammar :: Conditionals.Conditionals Domain Domain f,
      lambdaGrammar :: Lambda.Lambda Domain f}

data Tagged = IntExpression {intFromExpression :: Int}
            | BoolExpression {boolFromExpression :: Bool}
            | FunctionExpression {functionFromExpression :: Tagged -> Tagged}
            | TypeError String
            deriving (Eq, Ord, Show)

type Env = Map String Tagged

type Domain = Env -> Tagged

instance Eq (Tagged -> Tagged) where
   (==) = error "Can't compare fuctions"

instance Ord (Tagged -> Tagged) where
   (<=) = error "Can't compare fuctions"

instance Show (Tagged -> Tagged) where
   show _ = "function"

instance Arithmetic.ArithmeticDomain Tagged where
   number = IntExpression
   IntExpression a `add` IntExpression b = IntExpression (a+b)
   _ `add` _ = TypeError "type error: add expects numbers"
   IntExpression a `multiply` IntExpression b = IntExpression (a*b)
   _ `multiply` _ = TypeError "type error: multiply expects numbers"
   negate (IntExpression a) = IntExpression (Prelude.negate a)
   negate _ = TypeError "type error: negate expects a number"
   IntExpression a `subtract` IntExpression b = IntExpression (a-b)
   _ `subtract` _ = TypeError "type error: subtract expects numbers"
   IntExpression a `divide` IntExpression b = IntExpression (div a b)
   _ `divide` _ = TypeError "type error: divide expects numbers"

instance Arithmetic.ArithmeticDomain (Env -> Tagged) where
   number n _ = IntExpression n
   (a `add` b) env = case (a env, b env)
                     of (IntExpression a', IntExpression b') -> IntExpression (a' + b')
                        _ -> TypeError "type error: add expects numbers"
   (a `multiply` b) env = case (a env, b env)
                          of (IntExpression a', IntExpression b') -> IntExpression (a' * b')
                             _ -> TypeError "type error: multiply expects numbers"
   negate a env = case a env
                  of IntExpression a' -> IntExpression (Prelude.negate a')
                     _ -> TypeError "type error: negate expects a number"
   (a `subtract` b) env = case (a env, b env)
                          of (IntExpression a', IntExpression b') -> IntExpression (a' - b')
                             _ -> TypeError "type error: subtract expects numbers"
   (a `divide` b) env = case (a env, b env)
                        of (IntExpression a', IntExpression b') -> IntExpression (div a' b')
                           _ -> TypeError "type error: divide expects numbers"

instance Boolean.BooleanDomain (Env -> Tagged) where
   true _ = BoolExpression True
   false _ = BoolExpression False
   (a `and` b) env = case (a env, b env)
                     of (BoolExpression a', BoolExpression b') -> BoolExpression (a' && b')
                        _ -> TypeError "type error: and expects booleans"
   (a `or` b) env = case (a env, b env)
                    of (BoolExpression a', BoolExpression b') -> BoolExpression (a' || b')
                       _ -> TypeError "type error: r expects booleans"
   not a env = case a env
               of BoolExpression a' -> BoolExpression (Data.Bool.not a')
                  _ -> TypeError "type error: not expects a boolean"

instance Comparisons.ComparisonDomain Domain Domain  where
   greaterThan a b env = BoolExpression (a env > b env)
   lessThan a b env = BoolExpression (a env < b env)
   equal a b env = BoolExpression (a env == b env)
   greaterOrEqual a b env = BoolExpression (a env >= b env)
   lessOrEqual a b env = BoolExpression (a env <= b env)

instance Conditionals.ConditionalDomain Domain Domain where
   ifThenElse test t f env = case test env
                             of BoolExpression True -> t env
                                BoolExpression False -> f env
                                _ -> TypeError "type error: if expects a boolean"

instance Lambda.LambdaDomain (Env -> Tagged) where
   apply f arg env = case (f env, arg env)
                     of (FunctionExpression f', x) -> f' x
                        (f', _) -> TypeError ("Applying a non-function " ++ show f')
   lambda v body env = FunctionExpression (\arg-> body (Map.insert v arg env))
   var v env = Map.findWithDefault (TypeError $ "Free variable " ++ show v) v env

instance (Show (f Domain), Show (f String)) => Show (Expression f) where
   showsPrec prec g rest = "Expression{expr=" ++ showsPrec prec (expr g)
                           (", arithmeticGrammar=" ++ showsPrec prec (arithmeticGrammar g)
                           (", booleanGrammar=" ++ showsPrec prec (booleanGrammar g)
                           (", comparisonGrammar=" ++ showsPrec prec (comparisonGrammar g)
                           (", conditionalGrammar=" ++ showsPrec prec (conditionalGrammar g)
                           (", lambdaGrammar=" ++ showsPrec prec (lambdaGrammar g) ("}" ++ rest))))))

instance Rank2.Functor Expression where
   f <$> g = g{expr= f (expr g),
               term= f (term g),
               primary= f (primary g),
               arithmeticGrammar= Rank2.fmap f (arithmeticGrammar g),
               booleanGrammar= Rank2.fmap f (booleanGrammar g),
               comparisonGrammar= Rank2.fmap f (comparisonGrammar g),
               conditionalGrammar= Rank2.fmap f (conditionalGrammar g),
               lambdaGrammar= Rank2.fmap f (lambdaGrammar g)}

instance Rank2.Apply Expression where
   a <*> b = Expression{expr= expr a `Rank2.apply` expr b,
                        term= term a `Rank2.apply` term b,
                        primary= primary a `Rank2.apply` primary b,
                        arithmeticGrammar= arithmeticGrammar a `Rank2.ap` arithmeticGrammar b,
                        booleanGrammar= booleanGrammar a `Rank2.ap` booleanGrammar b,
                        comparisonGrammar= comparisonGrammar a `Rank2.ap` comparisonGrammar b,
                        conditionalGrammar= conditionalGrammar a `Rank2.ap` conditionalGrammar b,
                        lambdaGrammar= lambdaGrammar a `Rank2.ap` lambdaGrammar b}

instance Rank2.Applicative Expression where
   pure f = Expression{expr= f,
                       term= f,
                       primary= f,
                       arithmeticGrammar= Rank2.pure f,
                       booleanGrammar= Rank2.pure f,
                       comparisonGrammar= Rank2.pure f,
                       conditionalGrammar= Rank2.pure f,
                       lambdaGrammar= Rank2.pure f}

instance Rank2.Distributive Expression where
   distributeM f = Expression{expr= f >>= expr,
                              term= f >>= term,
                              primary= f >>= primary,
                              arithmeticGrammar= Rank2.distributeM (arithmeticGrammar <$> f),
                              booleanGrammar= Rank2.distributeM (booleanGrammar <$> f),
                              comparisonGrammar= Rank2.distributeM (comparisonGrammar <$> f),
                              conditionalGrammar= Rank2.distributeM (conditionalGrammar <$> f),
                              lambdaGrammar= Rank2.distributeM (lambdaGrammar <$> f)}
   distributeWith w f = Expression{expr= w (expr <$> f),
                                   term= w (term <$> f),
                                   primary= w (primary <$> f),
                                   arithmeticGrammar= Rank2.distributeWith w (arithmeticGrammar <$> f),
                                   booleanGrammar= Rank2.distributeWith w (booleanGrammar <$> f),
                                   comparisonGrammar= Rank2.distributeWith w (comparisonGrammar <$> f),
                                   conditionalGrammar= Rank2.distributeWith w (conditionalGrammar <$> f),
                                   lambdaGrammar= Rank2.distributeWith w (lambdaGrammar <$> f)}

instance Rank2.Foldable Expression where
   foldMap f g = f (expr g) <> f (term g) <> f (primary g)
                 <> Rank2.foldMap f (arithmeticGrammar g) <> Rank2.foldMap f (booleanGrammar g)
                 <> Rank2.foldMap f (comparisonGrammar g) <> Rank2.foldMap f (conditionalGrammar g)
                 <> Rank2.foldMap f (lambdaGrammar g)

instance Rank2.Traversable Expression where
   traverse f g = Expression
                  <$> f (expr g)
                  <*> f (term g)
                  <*> f (primary g)
                  <*> Rank2.traverse f (arithmeticGrammar g)
                  <*> Rank2.traverse f (booleanGrammar g)
                  <*> Rank2.traverse f (comparisonGrammar g)
                  <*> Rank2.traverse f (conditionalGrammar g)
                  <*> Rank2.traverse f (lambdaGrammar g)

expression :: GrammarBuilder Expression g String
expression Expression{..} =
   let combinedExpr = Arithmetic.expr arithmeticGrammar
                      <|> Boolean.expr booleanGrammar
                      <|> Conditionals.expr conditionalGrammar
                      <|> Lambda.expr lambdaGrammar
       combinedTerm = Lambda.application lambdaGrammar
                      <|> Arithmetic.sum arithmeticGrammar
       combinedPrimary = Arithmetic.primary arithmeticGrammar
                         <|> Boolean.factor booleanGrammar
                         <|> Lambda.primary lambdaGrammar
   in Expression{expr= combinedExpr,
                 term= combinedTerm,
                 primary= combinedPrimary,
                 arithmeticGrammar= Arithmetic.arithmetic arithmeticGrammar{Arithmetic.expr= expr,
                                                                            Arithmetic.primary= primary},
                 booleanGrammar= Boolean.boolean (Comparisons.test comparisonGrammar) booleanGrammar,
                 comparisonGrammar= Comparisons.comparisons comparisonGrammar{Comparisons.term= Arithmetic.expr arithmeticGrammar},
                 conditionalGrammar= Conditionals.conditionals conditionalGrammar{Conditionals.test= Boolean.expr booleanGrammar,
                                                                                  Conditionals.term= expr},
                 lambdaGrammar= Lambda.lambdaCalculus lambdaGrammar{Lambda.expr= expr,
                                                                    Lambda.application= term,
                                                                    Lambda.primary= primary}}
