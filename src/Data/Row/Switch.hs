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
  )
where

import Data.Row.Internal
import Data.Row.Records
import Data.Row.Variants



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
