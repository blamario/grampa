module Text.Grampa.ContextFree.LeftRecursive.Transformer (ParserT, SeparatedParser(..),
                                                          lift, liftPositive, tmap,
                                                          parseSeparated, separated)
where

import Control.Applicative (Alternative)
import Text.Grampa.ContextFree.LeftRecursive (Fixed, SeparatedParser(..), FallibleWithExpectations(..),
                                              liftPositive, liftPure, mapPrimitive, parseSeparated, separated)
import qualified Text.Grampa.ContextFree.SortedMemoizing.Transformer as Transformer
import Text.Grampa.ContextFree.SortedMemoizing.Transformer (ResultListT(ResultList), FailureInfo(FailureInfo))

type ParserT m = Fixed (Transformer.ParserT m)

-- | Lift a parse-free computation into the parser.
lift :: Applicative m => m a -> ParserT m g s a
lift = liftPure . Transformer.lift

-- | Modify the computation carried by the parser.
tmap :: (m a -> m a) -> ParserT m g s a -> ParserT m g s a
tmap = mapPrimitive . Transformer.tmap

instance FallibleWithExpectations (ResultListT m g) where
   hasSuccess (ResultList [] _) = False
   hasSuccess _ = True
   failureOf (ResultList _ failure) = failure
   failWith = ResultList []
   expectations (ResultList _ (FailureInfo _ expected)) = expected
