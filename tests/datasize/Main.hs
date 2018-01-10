module Main where

import Control.DeepSeq
import GHC.DataSize
import Test.Tasty
import Test.Tasty.HUnit

import Data.Row.Records


main :: IO ()
main = defaultMain $ testGroup "ghc-datasize"
    [ testCase "R0" $ do
        s  <- recursiveSize $!! ()
        s' <- recursiveSize $!! empty
        s @>=? s'
    , testCase "R1" $ do
        s  <- recursiveSize $!! True
        s' <- recursiveSize $!! ( #a .== True )
        s @>=? s'
    , testCase "R2" $ do
        let a = 1 :: Int
        s  <- recursiveSize $!! (a, True)
        s' <- recursiveSize $!! ( #a .== a .+ #b .== True )
        s @>=? s'
    , testCase "R3" $ do
        let a = 1 :: Int
            c = "Hello world"
        s  <- recursiveSize $!! (a, True, c)
        s' <- recursiveSize $!! ( #a .== a .+ #b .== True .+ #c .== c )
        s @>=? s'
    , testCase "R5" $ do
        s  <- recursiveSize $!! (7 :: Int, "blue", 'c', False, 3.14 :: Double)
        s' <- recursiveSize $!! ( #a .== (7 :: Int)
                               .+ #b .== "blue"
                               .+ #c .== 'c'
                               .+ #d .== False
                               .+ #e .== (3.14 :: Double) )
        s @>=? s'
    ]
    where x @>=? y = assertBool msg (10*x >= y)
            where msg = "Memory footprint greater than 10x of non-record: Non-record was "
                    ++ show x ++ " while record used " ++ show y
