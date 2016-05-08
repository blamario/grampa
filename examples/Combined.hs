{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             PartialTypeSignatures, RecordWildCards, ScopedTypeVariables, UndecidableInstances #-}

module Combined where

import Control.Applicative
import qualified Data.Bool
import Data.Monoid ((<>))
import Text.Grampa (Functor1(..), Foldable1(..), Traversable1(..), Reassemblable(..),
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

data Tagged = IntExpression Int
             | BoolExpression Bool
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
   applyFieldwise f a b = Expression{expr= expr (f b{expr= expr a}),
                                     arithmeticGrammar= applyFieldwise fa (arithmeticGrammar a) (arithmeticGrammar b),
                                     booleanGrammar= applyFieldwise fb (booleanGrammar a) (booleanGrammar b),
                                     comparisonGrammar= applyFieldwise fc (comparisonGrammar a) (comparisonGrammar b),
                                     conditionalGrammar= applyFieldwise fd (conditionalGrammar a)
                                                         (conditionalGrammar b)}
      where fa c = arithmeticGrammar (f $ b{arithmeticGrammar= c})
            fb c = booleanGrammar (f $ b{booleanGrammar= c})
            fc c = comparisonGrammar (f $ b{comparisonGrammar= c})
            fd c = conditionalGrammar (f $ b{conditionalGrammar= c})
   reassemble f g = Expression{expr= f expr (\e->g{expr= e}) g,
                               arithmeticGrammar= reassemble f1 (arithmeticGrammar g),
                               booleanGrammar= reassemble f2 (booleanGrammar g),
                               comparisonGrammar= reassemble f3 (comparisonGrammar g),
                               conditionalGrammar= reassemble f4 (conditionalGrammar g)}
      where f1 get set c = f (get . arithmeticGrammar) (\t->g{arithmeticGrammar= set t}) g{arithmeticGrammar= c}
            f2 get set c = f (get . booleanGrammar) (\t->g{booleanGrammar= set t}) g{booleanGrammar= c}
            f3 get set c = f (get . comparisonGrammar) (\t->g{comparisonGrammar= set t}) g{comparisonGrammar= c}
            f4 get set c = f (get . conditionalGrammar) (\t->g{conditionalGrammar= set t}) g{conditionalGrammar= c}

expression :: forall g. (Functor1 g) =>
              (Grammar g String -> Expression (Parser g String)) -> GrammarBuilder Expression g String
expression sub g =
   let arithmetic = Arithmetic.arithmetic
       comparisons = Comparisons.comparisons (production sub (Arithmetic.expr . arithmeticGrammar) g)
       boolean = Boolean.boolean (production sub ((BoolExpression <$>) . Comparisons.expr . comparisonGrammar) g)
       conditionals = Conditionals.conditionals (production sub (Boolean.expr . booleanGrammar) g) ( production sub ((IntExpression <$>) . Arithmetic.expr . arithmeticGrammar) g)
       expr' = expr
   in let Expression{..} = g
      in Expression{
            expr= IntExpression <$> Arithmetic.expr arithmeticGrammar
                  <|> Boolean.expr booleanGrammar
                  <|> BoolExpression <$> Comparisons.expr comparisonGrammar
                  <|> Conditionals.expr conditionalGrammar,
            arithmeticGrammar= arithmetic arithmeticGrammar,
            booleanGrammar= boolean booleanGrammar,
            comparisonGrammar= comparisons comparisonGrammar,
            conditionalGrammar= conditionals conditionalGrammar}
