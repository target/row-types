{-# LANGUAGE FunctionalDependencies #-}
-----------------------------------------------------------------------------
-- |
-- Module: Data.Row.Switch
--
-- This module provides the ability to discharge a polymorphic variant using
-- a record that has matching fields.
--
-----------------------------------------------------------------------------


module Data.Row.Switch
  (
    Switch(..)
  , SwitchU(..)
  )
where

import Data.Row.Internal
import Data.Row.Records
import Data.Row.Variants

import GHC.TypeLits


-- | A 'Var' and a 'Rec' can combine if their rows line up properly.
class Switch (v :: Row *) (r :: Row *) x | v x -> r, r x -> v where
  {-# MINIMAL switch | caseon #-}
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
    Right v -> switch v (unsafeRemove l r)
    where l = Label @l

-- | A 'Var' and a 'Rec' can combine if their rows line up properly.
-- For the "U" variant, we match uppercase variant names with lowercase
-- record names.  In other words, the variant name "Option1" would match with
-- the record name "option1".
class SwitchU (v :: Row *) (r :: Row *) x | v x -> r, r x -> v where
  {-# MINIMAL switchU | caseonU #-}
  -- | Given a Variant and a Record of functions from each possible value
  -- of the variant to a single output type, apply the correct
  -- function to the value in the variant.
  switchU :: Var v -> Rec r -> x
  switchU = flip caseonU
  -- | The same as @switch@ but with the argument order reversed
  caseonU :: Rec r -> Var v -> x
  caseonU = flip switchU


instance SwitchU (R '[]) (R '[]) x where
  switchU = const . impossible

instance ( KnownSymbol lv, KnownSymbol lr, SwitchU (R v) (R r) b
         , hv ~ Head lv, AppendSymbol hv tv ~ lv --Uncons lv hv tv
         , hr ~ Head lr, AppendSymbol hr tr ~ lr --Uncons lr hr tr
         , tv ~ tr, Lowercase hv ~ hr, Uppercase hr ~ hv)
      => SwitchU (R (lv :-> a ': v)) (R (lr :-> (a -> b) ': r)) b where
  switchU v r = case trial v lv of
    Left x  -> (r .! lr) x
    Right v -> switchU v (unsafeRemove lr r)
    where
      lv = Label @lv
      lr = Label @lr
