{-# Language GADTs #-}
module Text.Grampa.ContextFree.LeftRecursive.Transformer (ParserT, SeparatedParser(..), AmbiguityDecidable,
                                                          lift, liftPositive, tbind, tmap,
                                                          parseSeparated, separated)
where

import Text.Grampa.ContextFree.LeftRecursive (Fixed, SeparatedParser(..), FallibleWithExpectations(..),
                                              liftPositive, liftPure, mapPrimitive, parseSeparated, separated)
import qualified Text.Grampa.ContextFree.SortedMemoizing.Transformer as Transformer
import Text.Grampa.ContextFree.SortedMemoizing.Transformer (ResultListT(ResultList), FailureInfo(FailureInfo))
import Text.Grampa.Internal (AmbiguityDecidable)

type ParserT m = Fixed (Transformer.ParserT m)

-- | Lift a parse-free computation into the parser.
lift :: Applicative m => m a -> ParserT m g s a
lift = liftPure . Transformer.lift

-- | Transform the computation carried by the parser using the monadic bind ('>>=').
tbind :: (Monad m, AmbiguityDecidable b) => ParserT m g s a -> (a -> m b) -> ParserT m g s b
tbind p f = mapPrimitive (`Transformer.tbind` f) p

-- | Transform the computation carried by the parser.
tmap :: AmbiguityDecidable b => (m a -> m b) -> ParserT m g s a -> ParserT m g s b
tmap = mapPrimitive . Transformer.tmap

instance FallibleWithExpectations (ResultListT m g) where
   hasSuccess (ResultList [] _) = False
   hasSuccess _ = True
   failureOf (ResultList _ failure) = failure
   failWith = ResultList []
   expectations (ResultList _ (FailureInfo _ expected)) = expected
