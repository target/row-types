module Main (main) where

import Criterion.Main

import Data.String

import Data.Row.Records

type FourRecord a =
     "i0" .== a   .+ "i1" .== a   .+ "i2" .== a   .+ "i3"   .== a

type ElevenRecord a =
     "i0"  .== a  .+ "i1"  .== a  .+ "i2"  .== a  .+ "i3"   .== a
  .+ "i10" .== a  .+ "i11" .== a  .+ "i12" .== a  .+ "i13"  .== a
  .+ "i20" .== a  .+ "i21" .== a  .+ "i22" .== a

type SixteenRecord a =
     "i0"  .== a  .+ "i1"  .== a  .+ "i2"  .== a  .+ "i3"   .== a
  .+ "i10" .== a  .+ "i11" .== a  .+ "i12" .== a  .+ "i13"  .== a
  .+ "i20" .== a  .+ "i21" .== a  .+ "i22" .== a  .+ "i23"  .== a
  .+ "i30" .== a  .+ "i31" .== a  .+ "i32" .== a  .+ "i33"  .== a

-- type SixtyFourRecord a =
--      "i0"   .== a .+ "i1"   .== a .+ "i2"   .== a .+ "i3"   .== a
--   .+ "i10"  .== a .+ "i11"  .== a .+ "i12"  .== a .+ "i13"  .== a
--   .+ "i20"  .== a .+ "i21"  .== a .+ "i22"  .== a .+ "i23"  .== a
--   .+ "i30"  .== a .+ "i31"  .== a .+ "i32"  .== a .+ "i33"  .== a
--   .+ "i100" .== a .+ "i101" .== a .+ "i102" .== a .+ "i103" .== a
--   .+ "i110" .== a .+ "i111" .== a .+ "i112" .== a .+ "i113" .== a
--   .+ "i120" .== a .+ "i121" .== a .+ "i122" .== a .+ "i123" .== a
--   .+ "i130" .== a .+ "i131" .== a .+ "i132" .== a .+ "i133" .== a
--   .+ "i200" .== a .+ "i201" .== a .+ "i202" .== a .+ "i203" .== a
--   .+ "i210" .== a .+ "i211" .== a .+ "i212" .== a .+ "i213" .== a
--   .+ "i220" .== a .+ "i221" .== a .+ "i222" .== a .+ "i223" .== a
--   .+ "i230" .== a .+ "i231" .== a .+ "i232" .== a .+ "i233" .== a
--   .+ "i300" .== a .+ "i301" .== a .+ "i302" .== a .+ "i303" .== a
--   .+ "i310" .== a .+ "i311" .== a .+ "i312" .== a .+ "i313" .== a
--   .+ "i320" .== a .+ "i321" .== a .+ "i322" .== a .+ "i323" .== a
--   .+ "i330" .== a .+ "i331" .== a .+ "i332" .== a .+ "i333" .== a

-- my64Record :: Rec (SixtyFourRecord Double)
-- my64Record =
--      #i0   .== 0 .+ #i1   .== 0 .+ #i2   .== 0 .+ #i3   .== 0
--   .+ #i10  .== 0 .+ #i11  .== 0 .+ #i12  .== 0 .+ #i13  .== 0
--   .+ #i20  .== 0 .+ #i21  .== 0 .+ #i22  .== 0 .+ #i23  .== 0
--   .+ #i30  .== 0 .+ #i31  .== 0 .+ #i32  .== 0 .+ #i33  .== 0
--   .+ #i100 .== 0 .+ #i101 .== 0 .+ #i102 .== 0 .+ #i103 .== 0
--   .+ #i110 .== 0 .+ #i111 .== 0 .+ #i112 .== 0 .+ #i113 .== 0
--   .+ #i120 .== 0 .+ #i121 .== 0 .+ #i122 .== 0 .+ #i123 .== 0
--   .+ #i130 .== 0 .+ #i131 .== 0 .+ #i132 .== 0 .+ #i133 .== 0
--   .+ #i200 .== 0 .+ #i201 .== 0 .+ #i202 .== 0 .+ #i203 .== 0
--   .+ #i210 .== 0 .+ #i211 .== 0 .+ #i212 .== 0 .+ #i213 .== 0
--   .+ #i220 .== 0 .+ #i221 .== 0 .+ #i222 .== 0 .+ #i223 .== 0
--   .+ #i230 .== 0 .+ #i231 .== 0 .+ #i232 .== 0 .+ #i233 .== 0
--   .+ #i300 .== 0 .+ #i301 .== 0 .+ #i302 .== 0 .+ #i303 .== 0
--   .+ #i310 .== 0 .+ #i311 .== 0 .+ #i312 .== 0 .+ #i313 .== 0
--   .+ #i320 .== 0 .+ #i321 .== 0 .+ #i322 .== 0 .+ #i323 .== 0
--   .+ #i330 .== 0 .+ #i331 .== 0 .+ #i332 .== 0 .+ #i333 .== 0

main :: IO ()
main =
  defaultMain
    [ bgroup "Record Construction"
        [ bench "simple 1"  $ nf (#a .==) ()
        , bench "simple 4"  $ nf id $ #a .== () .+ #b .== () .+ #c .== () .+ #d .== ()
        , bench "reverse 4" $ nf id $ #d .== () .+ #c .== () .+ #b .== () .+ #a .== ()
        , bench "default 4" $ nf id $ default' @Num @(FourRecord Double) 0
        , bench "recordFromLabels 4" $ nf id $ fromLabels @IsString @(FourRecord String) (fromString . show)
        , bench "default 11" $ nf id $ default' @Num @(ElevenRecord Double) 0
        , bench "recordFromLabels 11" $ nf id $ fromLabels @IsString @(ElevenRecord String) (fromString . show)
        , bench "default 16" $ nf id $ default' @Num @(SixteenRecord Double) 0
        , bench "recordFromLabels 16" $ nf id $ fromLabels @IsString @(SixteenRecord String) (fromString . show)
        -- , bench "simple 64" $ nf id $ my64Record
        -- , bench "default 64" $ nf id $ default' @Num @(SixtyFourRecord Double) 0
        -- , bench "recordFromLabels 64" $ nf id $ fromLabels @IsString @(SixtyFourRecord String) (fromString . show)
        ]
    , bgroup "Record Append"
        [ bench "append 3 3" $ nf (uncurry (.+)) (#a .== () .+ #b .== () .+ #c .== (),   #d .== () .+ #e .== () .+ #f .== ())
        , bench "append 5 1" $ nf (uncurry (.+)) (#a .== () .+ #b .== () .+ #c .== () .+ #d .== () .+ #e .== (),   #f .== ())
        , bench "append 1 5" $ nf (uncurry (.+)) (#a .== (),   #b .== () .+ #c .== () .+ #d .== () .+ #e .== () .+ #f .== ())
        ]
    , bgroup "Record Access"
        [ bench "get 2 of 4" $ nf (.! #i1)     $ default' @Num @(FourRecord Double) 0
        , bench "get 7 of 11" $ nf (.! #i1)    $ default' @Num @(ElevenRecord Double) 0
        , bench "get 4 of 16" $ nf (.! #i10)   $ default' @Num @(SixteenRecord Double) 0
        , bench "get 16 of 16" $ nf (.! #i33)  $ default' @Num @(SixteenRecord Double) 0
        -- , bench "get 4 of 64" $ nf (.! #i10)   $ default' @Num @(SixtyFourRecord Double) 1
        -- , bench "get 45 of 64" $ nf (.! #i230) $ default' @Num @(SixtyFourRecord Double) 2
        -- , bench "get 63 of 64" $ nf (.! #i332) $ default' @Num @(SixtyFourRecord Double) 3
        ]
    , bgroup "Record Metamorphosis"
        [ bench "erase 4"  $ nf (erase @Show show) $ #a .== () .+ #b .== () .+ #c .== () .+ #d .== ()
        -- , bench "erase 64" $ nf (erase @Show show) $ my64Record
        ]
    ]
