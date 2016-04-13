module Main (main) where

import qualified Arithmetic (main)
import qualified Boolean (main)

main = Arithmetic.main >> Boolean.main
