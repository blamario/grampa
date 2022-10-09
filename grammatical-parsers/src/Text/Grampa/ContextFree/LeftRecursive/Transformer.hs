{-# Language GADTs #-}
-- | A context-free parser that can handle left-recursive grammars and carry a
-- monadic computation with each parsing result.
module Text.Grampa.ContextFree.LeftRecursive.Transformer (ParserT, SeparatedParser(..), AmbiguityDecidable,
                                                          lift, liftPositive, tbind, tmap,
                                                          autochain, parseSeparated, separated)
where

import Text.Grampa.ContextFree.LeftRecursive (Fixed, SeparatedParser(..),
                                              liftPositive, liftPure, mapPrimitive,
                                              autochain, parseSeparated, separated)
import qualified Text.Grampa.ContextFree.SortedMemoizing.Transformer as Transformer
import Text.Grampa.Internal (AmbiguityDecidable)

type ParserT m = Fixed (Transformer.ParserT m)

-- | Lift a parse-free computation into the parser.
lift :: (Applicative m, Ord s) => m a -> ParserT m g s a
lift = liftPure . Transformer.lift

-- | Transform the computation carried by the parser using the monadic bind ('>>=').
tbind :: (Monad m, AmbiguityDecidable b) => ParserT m g s a -> (a -> m b) -> ParserT m g s b
tbind p f = mapPrimitive (`Transformer.tbind` f) p

-- | Transform the computation carried by the parser.
tmap :: AmbiguityDecidable b => (m a -> m b) -> ParserT m g s a -> ParserT m g s b
tmap = mapPrimitive . Transformer.tmap
