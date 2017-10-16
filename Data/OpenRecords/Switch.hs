-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Variants
--
-- This module implements extensible variants using closed type famillies.
--
-----------------------------------------------------------------------------


module Data.OpenRecords.Switch
  (
    Switch(..)
  )
where

import Data.OpenRecords.Internal.Row
import Data.OpenRecords.Records
import Data.OpenRecords.Variants




class Switch (r :: Row *) (v :: Row *) x where
  -- | Given a Record of functions matching a Variant of values, apply the correct
  -- function to the value in the variant.
  switch :: Rec r -> Var v -> x

instance Switch r (R '[]) x where
  switch _ = impossible

instance (KnownSymbol l, HasType l (a -> b) r, Switch r (R v) b)
      => Switch r (R (l :-> a ': v)) b where
  switch r v = case trial v l of
    Left x  -> (r .! l) x
    Right v -> switch r v
    where l = Label :: Label l
