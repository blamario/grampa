{-# LANGUAGE FlexibleContexts, FlexibleInstances, InstanceSigs, MultiParamTypeClasses,
             PartialTypeSignatures, RankNTypes, RecordWildCards, ScopedTypeVariables, UndecidableInstances #-}

module Combined where

import Control.Applicative
import qualified Data.Bool
import Data.Monoid ((<>))
import Text.Grampa (Functor1(..), Foldable1(..), Traversable1(..), Apply1(..), Alternative1(..), Arrow1(..),
                    Reassemblable(..),
                    Grammar, GrammarBuilder, Parser, Production, production)
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
                           (", conditionalGrammar=" ++ showsPrec prec (conditionalGrammar g) "}"))))

instance Functor1 Expression where
   fmap1 f g = g{expr= f (expr g),
                 arithmeticGrammar= fmap1 f (arithmeticGrammar g),
                 booleanGrammar= fmap1 f (booleanGrammar g),
                 comparisonGrammar= fmap1 f (comparisonGrammar g),
                 conditionalGrammar= fmap1 f (conditionalGrammar g)}

instance Apply1 Expression where
   ap1 a b = Expression{expr= expr a `apply1` expr b,
                        arithmeticGrammar= arithmeticGrammar a `ap1` arithmeticGrammar b,
                        booleanGrammar= booleanGrammar a `ap1` booleanGrammar b,
                        comparisonGrammar= comparisonGrammar a `ap1` comparisonGrammar b,
                        conditionalGrammar= conditionalGrammar a `ap1` conditionalGrammar b}

instance Alternative1 Expression where
   empty1 = Expression{expr= empty,
                       arithmeticGrammar= empty1,
                       booleanGrammar= empty1,
                       comparisonGrammar= empty1,
                       conditionalGrammar= empty1}
   choose1 a b = Expression{expr= expr a <|> expr b,
                            arithmeticGrammar= arithmeticGrammar a `choose1` arithmeticGrammar b,
                            booleanGrammar= booleanGrammar a `choose1` booleanGrammar b,
                            comparisonGrammar= comparisonGrammar a `choose1` comparisonGrammar b,
                            conditionalGrammar= conditionalGrammar a `choose1` conditionalGrammar b}

instance Foldable1 Expression where
   foldMap1 f g = f (expr g) <> foldMap1 f (arithmeticGrammar g) <> foldMap1 f (booleanGrammar g)
                  <> foldMap1 f (comparisonGrammar g) <> foldMap1 f (conditionalGrammar g)

instance Traversable1 Expression where
   traverse1 f g = Expression
                   <$> f (expr g)
                   <*> traverse1 f (arithmeticGrammar g)
                   <*> traverse1 f (booleanGrammar g)
                   <*> traverse1 f (comparisonGrammar g)
                   <*> traverse1 f (conditionalGrammar g)

instance Reassemblable Expression where
   reassemble :: forall p q. (forall a. (forall f. Expression f -> f a) -> Expression p -> q a)
              -> Expression p -> Expression q
   reassemble f g = Expression{expr= f expr g,
                               arithmeticGrammar= reassemble f1 (arithmeticGrammar g),
                               booleanGrammar= reassemble f2 (booleanGrammar g),
                               comparisonGrammar= reassemble f3 (comparisonGrammar g),
                               conditionalGrammar= reassemble f4 (conditionalGrammar g)}
      where f1 :: (forall f. Arithmetic.Arithmetic Int f -> f a) -> Arithmetic.Arithmetic Int p -> q a
            f2 :: (forall f. Boolean.Boolean Tagged f -> f a) -> Boolean.Boolean Tagged p -> q a
            f3 :: (forall f. Comparisons.Comparisons Int Bool f -> f a) -> Comparisons.Comparisons Int Bool p -> q a
            f4 :: (forall f. Conditionals.Conditionals Tagged f -> f a) -> Conditionals.Conditionals Tagged p -> q a
            f1 get c = f (get . arithmeticGrammar) g{arithmeticGrammar= c}
            f2 get c = f (get . booleanGrammar) g{booleanGrammar= c}
            f3 get c = f (get . comparisonGrammar) g{comparisonGrammar= c}
            f4 get c = f (get . conditionalGrammar) g{conditionalGrammar= c}

expression :: forall g. (Functor1 g) =>
              (Grammar g String -> Expression (Parser g String)) -> GrammarBuilder Expression g String
expression sub g =
   let arithmetic = Arithmetic.arithmetic empty
       -- arithmetic = Arithmetic.arithmetic (production sub ((intFromExpression <$>) . recursive . expr) g)
       -- arithmetic = Arithmetic.arithmetic ((intFromExpression <$>) $ recursive $ expr g)
       comparisons = Comparisons.comparisons (production sub (Arithmetic.expr . arithmeticGrammar) g)
       boolean = Boolean.boolean (production sub ((BoolExpression <$>) . Comparisons.expr . comparisonGrammar) g)
       conditionals = Conditionals.conditionals (production sub expr g) (production sub expr g)
   in let Expression{..} = g
      in Expression{
            expr= IntExpression <$> Arithmetic.expr arithmeticGrammar
                  <|> Boolean.expr booleanGrammar
                  <|> Conditionals.expr conditionalGrammar,
            arithmeticGrammar= arithmetic arithmeticGrammar,
            booleanGrammar= boolean booleanGrammar,
            comparisonGrammar= comparisons comparisonGrammar,
            conditionalGrammar= conditionals conditionalGrammar}
