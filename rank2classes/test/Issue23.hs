{-# LANGUAGE TemplateHaskell #-}

module Issue23 (test) where

import Data.Functor.Identity
import Data.Functor.Classes
import qualified Rank2
import qualified Rank2.TH

import Test.Tasty (TestTree)
import Test.Tasty.HUnit (testCase, assertEqual)

data Stm r = Unit | ExpStmt (r Int) (Exp r)
data Exp r = Nil | Cons (r Bool) (Exp r) (Stm r)

instance Show1 r => Show (Stm r) where
  show Unit = "Unit"
  show (ExpStmt r e) = "(Stmt (" ++ showsPrec1 0 r (") " ++ show e ++ ")")
instance Show1 r => Show (Exp r) where
  show Nil = "Nil"
  show (Cons r e s) =
    "(Cons (" ++ showsPrec1 0 r (") " ++ show e ++ " " ++ show s ++ ")")

$(mconcat <$> traverse
  (\derive -> mconcat <$> traverse derive [''Stm, ''Exp])
  [ Rank2.TH.deriveFunctor
  , Rank2.TH.deriveFoldable
  , Rank2.TH.deriveTraversable
  ])

expToMaybe :: Exp Identity -> Exp Maybe
expToMaybe = Rank2.fmap (Just . runIdentity)

maybeToExp :: Exp Maybe -> Maybe (Exp Identity)
maybeToExp = Rank2.traverse (fmap Identity)

myExp :: Exp Identity
myExp = Cons
  (Identity True)
  (Cons (Identity False) Nil (ExpStmt (Identity 2) Nil))
  (ExpStmt (Identity 3) (Cons (Identity True) Nil Unit))

test :: TestTree
test = testCase "Issue #23" $ do
  print myExp
  let myExp' = expToMaybe myExp
  assertEqual "" (show $ Just myExp) (show $ maybeToExp myExp')
