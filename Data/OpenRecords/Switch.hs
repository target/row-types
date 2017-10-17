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



-- | A 'Var' and a 'Rec' can combine if their rows line up properly.
class Switch (v :: Row *) (r :: Row *) x where
  -- | Given a Variant and a Record of functions from each possible value
  -- of the variant to a single output type, apply the correct
  -- function to the value in the variant.
  switch :: Var v -> Rec r -> x

instance Switch (R '[]) r x where
  switch = const . impossible

instance (KnownSymbol l, HasType l (a -> b) r, Switch (R v) r b)
      => Switch (R (l :-> a ': v)) r b where
  switch v r = case trial v l of
    Left x  -> (r .! l) x
    Right v -> switch v r
    where l = Label :: Label l
