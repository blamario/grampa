{-# LANGUAGE Haskell2010, BangPatterns, ExistentialQuantification, FlexibleContexts, OverloadedStrings,
  RecordWildCards, ScopedTypeVariables, TemplateHaskell #-}

module Benchmark where

import Control.Applicative
import Data.Functor.Compose (Compose(..))
import Data.Monoid ((<>))

import Control.DeepSeq (deepseq)
import Criterion.Main (bench, bgroup, defaultMain, nf)

import qualified Rank2
import qualified Rank2.TH

import Text.Parser.Combinators (eof)
import Text.Grampa
import Text.Grampa.ContextFree.Parallel (Parser)
import qualified Arithmetic
import qualified Boolean
import Main (arithmetic, boolean)

data Recursive f = Recursive{start :: f String,
                             rec :: f String,
                             next :: f String}

$(Rank2.TH.deriveAll ''Recursive)

recursiveManyGrammar :: Recursive (Parser g String) -> Recursive (Parser g String)
recursiveManyGrammar Recursive{..} = Recursive{
   start= rec <* eof,
   rec= many (char ';') <* optional next,
   next= string "END"}

parseInt :: String -> [Int]
parseInt s = case Arithmetic.expr (parseComplete (fixGrammar arithmetic) s)
             of Compose (Right [r]) -> [r]
                r -> error ("Unexpected " <> show r)

parseBoolean :: String -> [Bool]
parseBoolean s = case (Boolean.expr . Rank2.snd) (parseComplete (fixGrammar boolean) s)
                 of Compose (Right [r]) -> [r]
                    r -> error ("Unexpected " <> show r)

zeroes, ones, falsehoods, truths, groupedLeft, groupedRight :: Int -> String
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
{-
      bgroup "many" [
          bench "simple" $ nf (simpleParse $ many (string ";") <* endOfInput) (replicate 400 ';'),
          bench "recursive" $ nf (parse (fixGrammar recursiveManyGrammar) start) (replicate 400 ';')],
-}
      bgroup "zero sum" [
         bench "100" $ nf parseInt zeroes100,
         bench "200" $ nf parseInt zeroes200,
         bench "300" $ nf parseInt zeroes300],
      bgroup "grouped left" [
         bench "100" $ nf parseInt groupedLeft100,
         bench "200" $ nf parseInt groupedLeft200,
         bench "300" $ nf parseInt groupedLeft300],
{-
      bgroup "grouped right" [
            bench "100" $ nf parseInt groupedRight100,
            bench "200" $ nf parseInt groupedRight200,
            bench "300" $ nf parseInt groupedRight300],
-}
      bgroup "one product" [
         bench "100" $ nf parseInt ones100,
         bench "200" $ nf parseInt ones200,
         bench "300" $ nf parseInt ones300],
      bgroup "false disjunction" [
         bench "80" $ nf parseBoolean falsehoods80,
         bench "160" $ nf parseBoolean falsehoods160,
         bench "240" $ nf parseBoolean falsehoods240]
      ]
   
