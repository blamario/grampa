{-# LANGUAGE Haskell2010 #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE KindSignatures, PolyKinds, StandaloneDeriving, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

--module Issue32 where

import Data.Functor.Compose
import Data.Functor.Identity
import Data.Kind (Type)
import Data.Void
import qualified Rank2.TH
import qualified Transformation.Deep
import qualified Transformation.Deep.TH
import qualified Transformation.Rank2

import Test.Tasty (TestTree, defaultMain)
import Test.Tasty.HUnit (testCase, assertEqual)

data Param d s = Param
  { key :: s String,
    val :: s String
  }

deriving instance Eq (s String) => Eq (Param d s)
deriving instance Show (s String) => Show (Param d s)

Rank2.TH.deriveFunctor ''Param
Rank2.TH.deriveFoldable ''Param
Rank2.TH.deriveTraversable ''Param
Transformation.Deep.TH.deriveFunctor ''Param
Transformation.Deep.TH.deriveFoldable ''Param
Transformation.Deep.TH.deriveTraversable ''Param

param :: Param x Identity
param = Param {key = Identity "Hello", val = Identity "World"}

test :: TestTree
test = testCase "Issue #32" $ do
  print param
  assertEqual ""
    (Just param)
    (Transformation.Deep.traverse (Transformation.Rank2.Map (Compose . Just)) param)

main = defaultMain test
