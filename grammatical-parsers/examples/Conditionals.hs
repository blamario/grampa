{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RecordWildCards,
             TypeFamilies, TemplateHaskell #-}
module Conditionals where

import Control.Applicative
import Data.Monoid ((<>))

import qualified Rank2.TH

import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive (Parser)

class ConditionalDomain c e where
   ifThenElse :: c -> e -> e -> e

instance ConditionalDomain Bool e where
   ifThenElse True t _ = t
   ifThenElse False _ f = f

instance ConditionalDomain [Char] [Char] where
   ifThenElse cond t f = "if " <> cond <> " then " <> t <> " else " <> f

data Conditionals t e f = Conditionals{expr :: f e,
                                       test :: f t,
                                       term :: f e}

instance (Show (f t), Show (f e)) => Show (Conditionals t e f) where
   showsPrec prec a rest = "Conditionals{expr=" ++ showsPrec prec (expr a)
                           (", test= " ++ showsPrec prec (test a)
                            (", term= " ++ showsPrec prec (term a) ("}" ++ rest)))

$(Rank2.TH.deriveAll ''Conditionals)

instance TokenParsing (Parser (Conditionals t e) String)
instance LexicalParsing (Parser (Conditionals t e) String)

conditionals :: (ConditionalDomain t e, LexicalParsing (Parser g String))
             => GrammarBuilder (Conditionals t e) g Parser String
conditionals Conditionals{..} =
   Conditionals{expr= ifThenElse <$> (keyword "if" *> test) <*> (keyword "then" *> term) <*> (keyword "else" *> term),
                test= empty,
                term= empty}
