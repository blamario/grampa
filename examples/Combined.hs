{-# LANGUAGE FlexibleContexts, FlexibleInstances, InstanceSigs, MultiParamTypeClasses,
             PartialTypeSignatures, RankNTypes, RecordWildCards, ScopedTypeVariables, UndecidableInstances #-}

module Combined where

import Control.Applicative
import qualified Data.Bool
import Data.Monoid ((<>))
import qualified Rank2
import Text.Grampa (Grammar, GrammarBuilder, Parser)
import Arithmetic (Arithmetic)
import qualified Arithmetic
import qualified Boolean
import qualified Comparisons
import qualified Conditionals

data Expression f =
   Expression{
      expr :: f Tagged,
      arithmeticGrammar :: Arithmetic.Arithmetic Int f,
      booleanGrammar :: Boolean.Boolean Tagged f,
      comparisonGrammar :: Comparisons.Comparisons Int Bool f,
      conditionalGrammar :: Conditionals.Conditionals Tagged f}

data Tagged = IntExpression {intFromExpression :: Int}
             | BoolExpression {boolFromExpression :: Bool}
               deriving Show

instance Boolean.BooleanDomain Tagged where
   true = BoolExpression True
   false = BoolExpression False
   BoolExpression x `and` BoolExpression y = BoolExpression (x && y)
   BoolExpression x `or` BoolExpression y = BoolExpression (x || y)
   not (BoolExpression x) = BoolExpression (Data.Bool.not x)

instance Conditionals.ConditionalDomain Tagged e where
   ifThenElse (BoolExpression True) t _ = t
   ifThenElse (BoolExpression False) _ f = f

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

instance Rank2.Reassemblable Expression where
   reassemble :: forall p q. (forall a. (forall f. Expression f -> f a) -> Expression p -> q a)
              -> Expression p -> Expression q
   reassemble f g = Expression{expr= f expr g,
                               arithmeticGrammar= Rank2.reassemble f1 (arithmeticGrammar g),
                               booleanGrammar= Rank2.reassemble f2 (booleanGrammar g),
                               comparisonGrammar= Rank2.reassemble f3 (comparisonGrammar g),
                               conditionalGrammar= Rank2.reassemble f4 (conditionalGrammar g)}
      where f1 :: (forall f. Arithmetic.Arithmetic Int f -> f a) -> Arithmetic.Arithmetic Int p -> q a
            f2 :: (forall f. Boolean.Boolean Tagged f -> f a) -> Boolean.Boolean Tagged p -> q a
            f3 :: (forall f. Comparisons.Comparisons Int Bool f -> f a) -> Comparisons.Comparisons Int Bool p -> q a
            f4 :: (forall f. Conditionals.Conditionals Tagged f -> f a) -> Conditionals.Conditionals Tagged p -> q a
            f1 get c = f (get . arithmeticGrammar) g{arithmeticGrammar= c}
            f2 get c = f (get . booleanGrammar) g{booleanGrammar= c}
            f3 get c = f (get . comparisonGrammar) g{comparisonGrammar= c}
            f4 get c = f (get . conditionalGrammar) g{conditionalGrammar= c}

expression :: forall g. (Rank2.Functor g) =>
              (Grammar g String -> Expression (Parser g String)) -> GrammarBuilder Expression g String
expression sub g =
   let arithmetic = Arithmetic.arithmetic empty
       -- arithmetic = Arithmetic.arithmetic (production sub ((intFromExpression <$>) . recursive . expr) g)
       -- arithmetic = Arithmetic.arithmetic ((intFromExpression <$>) $ recursive $ expr g)
       comparisons = Comparisons.comparisons ((Arithmetic.expr . arithmeticGrammar) g)
       boolean = Boolean.boolean (((BoolExpression <$>) . Comparisons.expr . comparisonGrammar) g)
       conditionals = Conditionals.conditionals (expr g) (expr g)
   in let Expression{..} = g
      in Expression{
            expr= IntExpression <$> Arithmetic.expr arithmeticGrammar
                  <|> Boolean.expr booleanGrammar
                  <|> Conditionals.expr conditionalGrammar,
            arithmeticGrammar= arithmetic arithmeticGrammar,
            booleanGrammar= boolean booleanGrammar,
            comparisonGrammar= comparisons comparisonGrammar,
            conditionalGrammar= conditionals conditionalGrammar}
