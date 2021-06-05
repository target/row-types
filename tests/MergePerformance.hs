module MergePerformance where

import Data.Row

type Key l = l .== ()
type Common = Key "z" .\/ Key "x" .\/ Key "y" .\/ Key "m" .\/ Key "n" .\/ Key "q" .\/ Key "v"
type Ext l  = Common .\/ Key l

type A = Ext "a" .\/ Ext "b" .\/ Ext "c" .\/ Ext "d" .\/ Ext "e" .\/ Ext "f" .\/ Ext "g" .\/ Ext "h" .\/ Ext "i"

test :: Rec (Common .+ A) -> Rec (Common .+ A)
test = id

