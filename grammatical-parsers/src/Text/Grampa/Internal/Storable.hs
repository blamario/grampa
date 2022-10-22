{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Text.Grampa.Internal.Storable (Storable(..), Storable1(..), Storable11(..),
                                      Dependencies(..), ParserFlags(..)) where

import Data.Functor.Const (Const(Const, getConst))
import qualified Rank2
import Text.Grampa.Class (ParseFailure(ParseFailure))
import Text.Grampa.Internal (ResultList(ResultList), ResultsOfLength(ResultsOfLength),
                             ParserFlags (ParserFlags, nullable, dependsOn),
                             Dependencies (DynamicDependencies, StaticDependencies))
import qualified Text.Grampa.ContextFree.SortedMemoizing.Transformer as Transformer

class Storable s a where
   store :: a -> s
   reuse :: s -> a

class Storable1 s a where
   store1 :: a -> s b
   reuse1 :: s b -> a

class Storable11 s t where
   store11 :: t a -> s b
   reuse11 :: s b -> t a

instance Storable a a where
   store = id
   reuse = id

instance Storable1 (Const a) a where
   store1 = Const
   reuse1 = getConst

instance Storable1 s a => Storable11 s (Const a) where
   store11 = store1 . getConst
   reuse11 = Const . reuse1

instance (Storable1 f a, Rank2.Functor g) => Storable (g f) (g (Const a)) where
   store = Rank2.fmap (store1 . getConst)
   reuse = Rank2.fmap (Const . reuse1)

instance Ord s => Storable1 (ResultList g s) Bool where
   store1 bit = ResultList [] (ParseFailure (if bit then 1 else 0) mempty [])
   reuse1 (ResultList _ (ParseFailure pos _ _)) = pos /= 0

instance (Rank2.Functor g, Monoid s, Ord s) => Storable1 (ResultList g s) (ParserFlags g) where
   store1 a = ResultList [store a] mempty
   reuse1 (ResultList [s] _) = reuse s

instance (Rank2.Functor g, Monoid s, Ord s) => Storable (ResultsOfLength g s r) (ParserFlags g) where
   store (ParserFlags n d) = ResultsOfLength (if n then 1 else 0) (store d) (pure $ error "unused")
   reuse (ResultsOfLength n d _) = ParserFlags (n /= 0) (reuse d)

instance (Rank2.Functor g, Monoid s, Ord s) => Storable [(s, g (ResultList g s))] (Dependencies g) where
   store DynamicDependencies = []
   store (StaticDependencies deps) = [(mempty, store deps)]
   reuse [] = DynamicDependencies
   reuse [(_, deps)] = StaticDependencies (reuse deps)

instance Ord s => Storable1 (Transformer.ResultListT m g s) Bool where
   store1 bit = Transformer.ResultList [] (ParseFailure (if bit then 1 else 0) mempty [])
   reuse1 (Transformer.ResultList _ (ParseFailure pos _ _)) = pos /= 0

instance (Rank2.Functor g, Monoid s, Ord s) => Storable1 (Transformer.ResultListT m g s) (ParserFlags g) where
   store1 a = Transformer.ResultList [store a] mempty
   reuse1 (Transformer.ResultList [s] _) = reuse s

instance (Rank2.Functor g, Monoid s, Ord s) => Storable (Transformer.ResultsOfLengthT m g s r) (ParserFlags g) where
   store = Transformer.ResultsOfLengthT . store
   reuse = reuse . Transformer.getResultsOfLength

instance (Rank2.Functor g, Monoid s, Ord s) => Storable (Transformer.ResultsOfLength m g s r) (ParserFlags g) where
   store (ParserFlags n d) = Transformer.ROL (if n then 1 else 0) (store d) (pure $ error "unused")
   reuse (Transformer.ROL n d _) = ParserFlags (n /= 0) (reuse d)

instance (Rank2.Functor g, Monoid s, Ord s) => Storable [(s, g (Transformer.ResultListT m g s))] (Dependencies g) where
   store DynamicDependencies = []
   store (StaticDependencies deps) = [(mempty, store deps)]
   reuse [] = DynamicDependencies
   reuse [(_, deps)] = StaticDependencies (reuse deps)
