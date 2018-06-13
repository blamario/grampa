{-# LANGUAGE KindSignatures, RankNTypes, TemplateHaskell #-}

import Control.Applicative (liftA2)
import Data.Foldable (fold, foldMap)
import Data.Traversable (traverse)
import Data.Distributive (cotraverse)
import Data.Monoid (Dual, Sum(Sum), getDual)
import Data.Functor.Classes (Eq1, Show1, eq1, showsPrec1)
import Data.Functor.Compose (Compose(Compose))
import Data.Functor.Identity (Identity(Identity, runIdentity))
import qualified Rank2
import qualified Rank2.TH
import Test.Tasty
import Test.Tasty.HUnit

data Test0 (p :: * -> *) = Test0{} deriving (Eq, Show)

data Test1 p = Test1{single     :: p Int,
                     whole      :: Test0 p,
                     wrapSingle :: Dual (Identity (p String)),
                     wrapWhole  :: Sum (Identity (Test0 p))}

instance Eq1 p => Eq (Test1 p) where
   a == b = single a `eq1` single b
            && whole a == whole b
            && all (all id) (liftA2 (liftA2 eq1) (wrapSingle a) (wrapSingle b))
            && wrapWhole a == wrapWhole b

instance Show1 p => Show (Test1 p) where
   showsPrec p t s = "Test1{single= " ++ showsPrec1 p (single t)
                     (", whole= " ++ showsPrec p (whole t)
                      (", wrapSingle= Dual (Identity (" ++ showsPrec1 p (runIdentity $ getDual $ wrapSingle t)
                       (")), wrapWhole= " ++ showsPrec p (wrapWhole t) s)))

$(Rank2.TH.deriveAll ''Test0)
$(Rank2.TH.deriveAll ''Test1)

main = defaultMain $ testCase "Template test" $
       do let test = Test1{single= [3, 4, 5],
                           whole= Test0,
                           wrapSingle= pure (pure ["a", "b", "ab"]),
                           wrapWhole= pure (pure Test0)}
          id Rank2.<$> test @?= test
          Rank2.pure (Rank2.Arrow id) Rank2.<*> test @?= test
          Rank2.liftA2 (++) test test @?= Test1{single= [3, 4, 5, 3, 4, 5],
                                                whole= Test0,
                                                wrapSingle= pure (pure ["a", "b", "ab", "a", "b", "ab"]),
                                                wrapWhole= pure (pure Test0)}
          Rank2.foldMap (Sum . length) test @?= Sum 6
          Rank2.traverse (map Identity) test @?= [Test1{single= Identity 3,
                                                        whole= Test0,
                                                        wrapSingle= pure (pure $ Identity "a"),
                                                        wrapWhole= pure (pure Test0)},
                                                  Test1{single= Identity 3,
                                                        whole= Test0,
                                                        wrapSingle= pure (pure $ Identity "b"),
                                                        wrapWhole= pure (pure Test0)},
                                                  Test1{single= Identity 3,
                                                        whole= Test0,
                                                        wrapSingle= pure (pure $ Identity "ab"),
                                                        wrapWhole= pure (pure Test0)},
                                                  Test1{single= Identity 4,
                                                        whole= Test0,
                                                        wrapSingle= pure (pure $ Identity "a"),
                                                        wrapWhole= pure (pure Test0)},
                                                  Test1{single= Identity 4,
                                                        whole= Test0,
                                                        wrapSingle= pure (pure $ Identity "b"),
                                                        wrapWhole= pure (pure Test0)},
                                                  Test1{single= Identity 4,
                                                        whole= Test0,
                                                        wrapSingle= pure (pure $ Identity "ab"),
                                                        wrapWhole= pure (pure Test0)},
                                                  Test1{single= Identity 5,
                                                        whole= Test0,
                                                        wrapSingle= pure (pure $ Identity "a"),
                                                        wrapWhole= pure (pure Test0)},
                                                  Test1{single= Identity 5,
                                                        whole= Test0,
                                                        wrapSingle= pure (pure $ Identity "b"),
                                                        wrapWhole= pure (pure Test0)},
                                                  Test1{single= Identity 5,
                                                        whole= Test0,
                                                        wrapSingle= pure (pure $ Identity "ab"),
                                                        wrapWhole= pure (pure Test0)}
                                                   ]
          Rank2.distribute (Identity test) @?= Test1{single= Compose (Identity [3, 4, 5]),
                                                     whole= Test0,
                                                     wrapSingle= pure (pure $ Compose $ Identity ["a", "b", "ab"]),
                                                     wrapWhole= pure (pure Test0)}
          Rank2.cotraverse (take 1 . map runIdentity) (Rank2.traverse (map Identity) test) @?= take 1 Rank2.<$> test
