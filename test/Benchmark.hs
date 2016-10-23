{-# LANGUAGE Haskell2010, BangPatterns, ExistentialQuantification, FlexibleContexts, OverloadedStrings,
  ScopedTypeVariables #-}

module Benchmark where

import Control.Applicative (empty)
import Data.Monoid ((<>))

import Control.DeepSeq (deepseq)
import Criterion.Main (bench, bgroup, defaultMain, nf)

import qualified Rank2
import Text.Grampa hiding (parse)
import qualified Arithmetic
import qualified Boolean
import Main (arithmetic, boolean)

parse :: String -> [Int]
parse s = case parseAll (fixGrammar $ arithmetic empty) Arithmetic.expr s
          of Right [r] -> [r]
             r -> error ("Unexpected " <> show r)

parseBoolean :: String -> [Bool]
parseBoolean s = case parseAll (fixGrammar boolean) (Boolean.expr . Rank2.snd) s
                 of Right [r] -> [r]
                    r -> error ("Unexpected " <> show r)

zeroes n = "0" <> concat (replicate n "+0")
ones n = "1" <> concat (replicate n "*1")
falsehoods n = "False" <> concat (replicate n " || False")
truths n = "True" <> concat (replicate n " && True")

groupedLeft n = replicate n '(' <> "0" <> concat (replicate n "+0)")
groupedRight n = concat (replicate n "(0+") <> "0" <> replicate n ')'

main :: IO ()
main = do
   let zeroes100 = zeroes 100
       zeroes200 = zeroes 200
       zeroes300 = zeroes 300
       groupedLeft100 = groupedLeft 100
       groupedLeft200 = groupedLeft 200
       groupedLeft300 = groupedLeft 300
       groupedRight100 = groupedRight 100
       groupedRight200 = groupedRight 200
       groupedRight300 = groupedRight 300
       ones100 = ones 100
       ones200 = ones 200
       ones300 = ones 300
       falsehoods80 = falsehoods 80
       falsehoods160 = falsehoods 160
       falsehoods240 = falsehoods 240
   deepseq (zeroes100, zeroes200, zeroes300,
            groupedLeft100, groupedLeft200, groupedLeft300,
            groupedRight100, groupedRight200, groupedRight300) $
      defaultMain [
      bgroup "zero sum" [
            bench "100" $ nf parse zeroes100,
            bench "200" $ nf parse zeroes200,
            bench "300" $ nf parse zeroes300],
      bgroup "grouped left" [
            bench "100" $ nf parse groupedLeft100,
            bench "200" $ nf parse groupedLeft200,
            bench "300" $ nf parse groupedLeft300],
{-
      bgroup "grouped right" [
            bench "100" $ nf parse groupedRight100,
            bench "200" $ nf parse groupedRight200,
            bench "300" $ nf parse groupedRight300],
-}
      bgroup "one product" [
            bench "100" $ nf parse ones100,
            bench "200" $ nf parse ones200,
            bench "300" $ nf parse ones300],
      bgroup "false disjunction" [
            bench "80" $ nf parseBoolean falsehoods80,
            bench "160" $ nf parseBoolean falsehoods160,
            bench "240" $ nf parseBoolean falsehoods240]
      ]
   
