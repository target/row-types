
-- The old implementation of MinJoinR and ConstUnionR (using Ifte) makes GHC blow up when there are
-- nested unions with many overlapping keys. The test suite checks this file with 1GB max heap,
-- which is plenty for the new implementation, but not nearly enough for the old.

module UnionPerformance where

import Data.Row

type Key l  = l .== ()
type Common = Key "a" .\/ Key "d" .\/ Key "f" .\/ Key "h" .\/ Key "k" .\/ Key "n" .\/ Key "q" .\/ Key "v"
type Ext l  = Common .\/ Key l

type MinJoin    = Ext "b" .\/ Ext "e" .\/ Ext "g" .\/ Ext "j" .\/ Ext "o" .\/ Ext "t" .\/ Ext "w"
type ConstUnion = Ext "b" .// Ext "e" .// Ext "g" .// Ext "j" .// Ext "o" .// Ext "t" .// Ext "w"

test :: Rec MinJoin -> Rec ConstUnion
test = id

