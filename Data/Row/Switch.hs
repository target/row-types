{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
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
  ( AppliesTo(..)
  , switch
  , caseon
  )
where

import Control.Arrow ((+++))
import Data.Proxy

import Data.Row.Internal
import Data.Row.Records
import Data.Row.Variants

-- | A simple class that we use to provide a constraint for function application.
class AppliesTo r f x | r x -> f, f r -> x where
  applyTo :: f -> x -> r
instance AppliesTo r (x -> r) x where
  applyTo = ($)

-- | A pair of a record and a variant.
data SwitchData r v = SwitchData (Rec r) (Var v)

-- | Like 'Const' but for two ignored type arguments.
newtype Const2 x y z = Const2 { getConst2 :: x }

-- | A 'Var' and a 'Rec' can combine if their rows line up properly.
-- Given a Variant along with a Record of functions from each possible value
-- of the variant to a single output type, apply the correct
-- function to the value in the variant.
switch :: forall v r x. BiForall r v (AppliesTo x) => Var v -> Rec r -> x
switch v r = getConst2 $ biMetamorph @_ @_ @r @v @(AppliesTo x) @Either @SwitchData @(Const2 x) @(Const2 x)
  Proxy doNil doUncons doCons $ SwitchData r v
  where
    doNil (SwitchData _ v) = impossible v
    doUncons :: forall ℓ f τ ϕ ρ. (KnownSymbol ℓ, AppliesTo x f τ, HasType ℓ f ϕ, HasType ℓ τ ρ)
             => Label ℓ -> SwitchData ϕ ρ -> Either (Const2 x f τ) (SwitchData (ϕ .- ℓ) (ρ .- ℓ))
    doUncons l (SwitchData r v) = (Const2 . applyTo (r .! l)) +++ (SwitchData $ lazyRemove l r) $ trial v l
    -- doCons :: forall ℓ f τ ϕ ρ. (KnownSymbol ℓ, AppliesTo x f τ)
    --        => Label ℓ -> Either (Const2 x f τ) (Const2 x ϕ ρ) -> Const2 x (Extend ℓ f ϕ) (Extend ℓ τ ρ)
    doCons _ (Left  (Const2 x)) = Const2 x
    doCons _ (Right (Const2 x)) = Const2 x

-- | The same as 'switch' but with the argument order reversed
caseon :: forall v r x. BiForall r v (AppliesTo x) => Rec r -> Var v -> x
caseon = flip switch
