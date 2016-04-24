{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RecordWildCards, ScopedTypeVariables #-}
module Conditionals where

import Control.Applicative
import Data.Monoid ((<>))

import Text.Grampa

class ConditionalDomain c e where
   ifThenElse :: c -> e -> e -> e

instance ConditionalDomain Bool e where
   ifThenElse True t _ = t
   ifThenElse False _ f = f

instance ConditionalDomain [Char] [Char] where
   ifThenElse cond t f = "(if " <> cond <> " then " <> t <> " else " <> f <> ")"

data Conditionals gTest gTerm e f =
   Conditionals{
      expr :: f e,
      test :: gTest f,
      term :: gTerm f}

instance (Show (f e), Show (gTest f), Show (gTerm f)) => Show (Conditionals gTest gTerm e f) where
   showsPrec prec a rest = "Conditionals{expr=" ++ showsPrec prec (expr a)
                           (", test=" ++ showsPrec prec (test a)
                            (", term=" ++ showsPrec prec (term a) ("}" ++ rest)))

instance (Functor1 gTest, Functor1 gTerm) => Functor1 (Conditionals gTest gTerm e) where
   fmap1 f a = a{expr= f (expr a),
                 test= fmap1 f (test a),
                 term= fmap1 f (term a)}

instance (Foldable1 gTest, Foldable1 gTerm) => Foldable1 (Conditionals gTest gTerm e) where
   foldMap1 f a = f (expr a) <> foldMap1 f (test a) <> foldMap1 f (term a)

instance (Traversable1 gTest, Traversable1 gTerm) => Traversable1 (Conditionals gTest gTerm e) where
   traverse1 f a = Conditionals
                   <$> f (expr a)
                   <*> traverse1 f (test a)
                   <*> traverse1 f (term a)

instance (Reassemblable gTest, Reassemblable gTerm) => Reassemblable (Conditionals gTest gTerm e) where
   composePer f g a = Conditionals{expr= expr (f a{expr= expr a'}),
                                   test= composePer f1 g1 (test a),
                                   term= composePer f2 g2 (term a)}
      where a' = g a
            f1 t = test (f $ a{test= t})
            g1 t = test (g $ a{test= t})
            f2 t = term (f $ a{term= t})
            g2 t = term (g $ a{term= t})
   reassemble f a = Conditionals{expr= f expr a,
                                 test= reassemble f1 (test a),
                                 term= reassemble f2 (term a)}
      where f1 get t = f (get . test) a{test= t}
            f2 get t = f (get . term) a{term= t}
   reassemble' f a = Conditionals{expr= f expr (\e->a{expr= e}) a,
                                 test= reassemble' f1 (test a),
                                 term= reassemble' f2 (term a)}
      where f1 get set t = f (get . test) (\t->a{test= set t}) a{test= t}
            f2 get set t = f (get . term) (\t->a{term= set t}) a{term= t}

conditionals :: (ConditionalDomain t e, Functor1 g, Functor1 gTest, Functor1 gTerm) =>
               GrammarBuilder gTest g String -> Production gTest (Parser g String) t
            -> GrammarBuilder gTerm g String -> Production gTerm (Parser g String) e
            -> GrammarBuilder (Conditionals gTest gTerm e) g String
conditionals testGrammar startTest termGrammar startTerm Conditionals{..} =
   let test' = startTest test
       term' = startTerm term
   in Conditionals{
            expr= ifThenElse <$> (string "if" *> test') <*> (string "then" *> term') <*> (string "else" *> term'),
            term= termGrammar term,
            test= testGrammar test}
