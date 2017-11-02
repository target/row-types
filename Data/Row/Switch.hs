{-# LANGUAGE FunctionalDependencies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Variants
--
-- This module implements extensible variants using closed type famillies.
--
-----------------------------------------------------------------------------


module Data.Row.Switch
  (
    Switch(..)
  )
where

import Data.Row.Internal
import Data.Row.Records
import Data.Row.Variants



-- | A 'Var' and a 'Rec' can combine if their rows line up properly.
-- A minimal complete definition is one of @switch@ or @caseon@
class Switch (v :: Row *) (r :: Row *) x | v x -> r, r x -> v where
  -- | Given a Variant and a Record of functions from each possible value
  -- of the variant to a single output type, apply the correct
  -- function to the value in the variant.
  switch :: Var v -> Rec r -> x
  switch = flip caseon
  -- | The same as @switch@ but with the argument order reversed
  caseon :: Rec r -> Var v -> x
  caseon = flip switch


instance Switch (R '[]) (R '[]) x where
  switch = const . impossible

instance (KnownSymbol l, Switch (R v) (R r) b)
      => Switch (R (l :-> a ': v)) (R (l :-> (a -> b) ': r)) b where
  switch v r = case trial v l of
    Left x  -> (r .! l) x
    Right v -> switch v (r .- l)
    where l = Label :: Label l
