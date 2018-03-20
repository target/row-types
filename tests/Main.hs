
module Main where

import Control.DeepSeq

import Data.Row.Records

-- We import Examples simply to make sure that the file typechecks.
import Examples ()

import Weigh

main :: IO ()
main = mainWith weights

-- | A helper function for validating the memory usage of inidividual values.
validateValue :: NFData a => String -> a -> (Weight -> Maybe String) -> Weigh ()
validateValue name m = validateFunc name (const m) ()

-- | The weights of records of size 1 through 5.
-- Currently, the maximum allowed allocations are much higher than I'd like.
weights :: Weigh ()
weights = do
  validateValue "empty" empty (maxAllocs 24)
  validateValue "R1"    ( #a .== True ) (maxAllocs 400)
  validateValue "R2"    ( #a .== (1 :: Int) .+ #b .== True ) (maxAllocs 800)
  validateValue "R3"    ( #a .== (1 :: Int) .+ #b .== True .+ #c .== "Hello" ) (maxAllocs 1700)
  validateValue "R5"    ( #a .== (7 :: Int)
                         .+ #b .== "blue"
                         .+ #c .== 'c'
                         .+ #d .== False
                         .+ #e .== (3.14 :: Double) )
                        (maxAllocs 2500)
