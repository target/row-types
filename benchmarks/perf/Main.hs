module Main (main) where

import Criterion.Main

import Data.Proxy
import Data.String

import Data.Row.Records

type FiveRecord a = "a" .== a .+ "b" .== a .+ "c" .== a .+ "d" .== a .+ "e" .== a

main :: IO ()
main =
  defaultMain
    [ bgroup "Record Construction"
        [ bench "simple 1"  $ nf (#a .==) ()
        , bench "simple 5"  $ nf id $ #a .== () .+ #b .== () .+ #c .== () .+ #d .== () .+ #e .== ()
        , bench "simple 10" $ nf id $ #a .== () .+ #b .== () .+ #c .== () .+ #d .== () .+ #e .== ()
                                   .+ #f .== () .+ #g .== () .+ #h .== () .+ #i .== () .+ #j .== ()
        , bench "reverse 5" $ nf id $ #e .== () .+ #d .== () .+ #c .== () .+ #b .== () .+ #a .== ()
        , bench "append 3 3" $ nf (uncurry (.+)) (#a .== () .+ #b .== () .+ #c .== (), #d .== () .+ #e .== () .+ #f .== ())
        , bench "default 5" $ nf id $ defaultRecord @Num @(FiveRecord Double) 0
        , bench "recordFromLabels 5" $ nf id $ recordFromLabels @IsString @(FiveRecord String) (fromString . show)
        ]
    , bgroup "Record Access"
        [ bench "get 1 of 5" $ nf (.! #a) $ #a .== () .+ #b .== () .+ #c .== () .+ #d .== () .+ #e .== ()
        , bench "get 5 of 5" $ nf (.! #e) $ #a .== () .+ #b .== () .+ #c .== () .+ #d .== () .+ #e .== ()
        ]
    , bgroup "Record Metamorphosis"
        [ bench "erase" $ nf (erase (Proxy @Show) show) $ #a .== () .+ #b .== () .+ #c .== () .+ #d .== () .+ #e .== ()
        ]
    ]