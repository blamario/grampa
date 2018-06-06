{-# LANGUAGE RankNTypes, TemplateHaskell #-}

import Control.Applicative (liftA2)
import Data.Foldable (foldMap)
import Data.Traversable (traverse)
import Data.Distributive (cotraverse)
import Data.Monoid ((<>))
import Data.Functor.Identity (Identity)
import qualified Rank2
import qualified Rank2.TH

data Test1 p = Test1{direct   :: p Int,
                     whole    :: Test1 p,
                     app      :: Identity (p String),
                     appWhole :: Identity (Test1 p)}

$(Rank2.TH.deriveAll ''Test1)

main = pure ()
