{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Row.Dictionaries
--
-- This module exports various dictionaries that help the type-checker when
-- dealing with row-types.
--
-----------------------------------------------------------------------------


module Data.Row.Dictionaries
  ( uniqueMap, uniqueAp, uniqueApSingle, uniqueZip
  , extendHas, mapHas, apHas, apSingleHas
  , mapExtendSwap, apExtendSwap, apSingleExtendSwap, zipExtendSwap
  , FreeForall
  , FreeBiForall
  , freeForall
  , mapForall
  , IsA(..)
  , As(..)
  -- * Re-exports
  , Dict(..), (:-)(..), HasDict(..), (\\), withDict
  )
where

import Data.Constraint
import Data.Proxy
import qualified Unsafe.Coerce as UNSAFE
import GHC.TypeLits

import Data.Row.Internal



-- | This data type is used to for its ability to existentially bind a type
-- variable.  Particularly, it says that for the type 'a', there exists a 't'
-- such that 'a ~ f t' and 'c t' holds.
data As c f a where
  As :: forall c f a t. (a ~ f t, c t) => As c f a

-- | A class to capture the idea of 'As' so that it can be partially applied in
-- a context.
class IsA c f a where
  as :: As c f a

instance c a => IsA c f (f a) where
  as = As

-- | An internal type used by the 'metamorph' in 'mapForall'.
newtype MapForall c f (r :: Row k) = MapForall { unMapForall :: Dict (Forall (Map f r) (IsA c f)) }

-- | This allows us to derive a `Forall (Map f r) ..` from a `Forall r ..`.
mapForall :: forall f c ρ. Forall ρ c :- Forall (Map f ρ) (IsA c f)
mapForall = Sub $ unMapForall $ metamorph @_ @ρ @c @FlipConst @Proxy @(MapForall c f) @Proxy Proxy empty uncons cons $ Proxy
  where empty _ = MapForall Dict
        uncons _ _ = FlipConst Proxy
        cons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, FrontExtends ℓ τ ρ, AllUniqueLabels (Extend ℓ τ ρ))
             => Label ℓ -> FlipConst (Proxy τ) (MapForall c f ρ)
             -> MapForall c f (Extend ℓ τ ρ)
        cons _ (FlipConst (MapForall Dict)) = case frontExtendsDict @ℓ @τ @ρ of
          FrontExtendsDict Dict -> MapForall Dict
            \\ mapExtendSwap @ℓ @τ @ρ @f
            \\ uniqueMap @(Extend ℓ τ ρ) @f

-- | Allow any 'Forall` over a row-type, be usable for 'Unconstrained1'.
freeForall :: forall r c. Forall r c :- Forall r Unconstrained1
freeForall = Sub $ UNSAFE.unsafeCoerce @(Dict (Forall r c)) Dict

type FreeForall r = Forall r Unconstrained1

type FreeBiForall r1 r2 = BiForall r1 r2 Unconstrained2

extendHas :: forall r l t. Dict (Extend l t r .! l ≈ t)
extendHas = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | This allows us to derive `Map f r .! l ≈ f t` from `r .! l ≈ t`
mapHas :: forall f r l t. (r .! l ≈ t) :- (Map f r .! l ≈ f t, Map f r .- l ≈ Map f (r .- l))
mapHas = Sub $ UNSAFE.unsafeCoerce $ Dict @(r .! l ≈ t)

-- | This allows us to derive `Ap ϕ ρ .! l ≈ f t` from `ϕ .! l ≈ f` and `ρ .! l ≈ t`
apHas :: forall ϕ ρ l f t. (ϕ .! l ≈ f, ρ .! l ≈ t) :- (Ap ϕ ρ .! l ≈ f t, Ap ϕ ρ .- l ≈ Ap (ϕ .- l) (ρ .- l))
apHas = Sub $ UNSAFE.unsafeCoerce $ Dict @(ϕ .! l ≈ f, ρ .! l ≈ t)

-- | This allows us to derive `ApSingle r x .! l ≈ f x` from `r .! l ≈ f`
apSingleHas :: forall r l f x. (r .! l ≈ f) :- (ApSingle r x .! l ≈ f x, ApSingle r x .- l ≈ ApSingle (r .- l) x)
apSingleHas = Sub $ UNSAFE.unsafeCoerce $ Dict @(r .! l ≈ f)

-- | Proof that the 'Map' type family preserves labels and their ordering.
mapExtendSwap :: forall ℓ τ r f. Dict (Extend ℓ (f τ) (Map f r) ≈ Map f (Extend ℓ τ r))
mapExtendSwap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Proof that the 'Ap' type family preserves labels and their ordering.
apExtendSwap :: forall ℓ (τ :: k) r (f :: k -> *) fs. Dict (Extend ℓ (f τ) (Ap fs r) ≈ Ap (Extend ℓ f fs) (Extend ℓ τ r))
apExtendSwap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Proof that the 'ApSingle' type family preserves labels and their ordering.
apSingleExtendSwap :: forall k ℓ (τ :: k) r (f :: k -> *). Dict (Extend ℓ (f τ) (ApSingle r τ) ≈ ApSingle (Extend ℓ f r) τ)
apSingleExtendSwap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Proof that the 'Ap' type family preserves labels and their ordering.
zipExtendSwap :: forall ℓ τ1 r1 τ2 r2. Dict (Extend ℓ (τ1, τ2) (Zip r1 r2) ≈ Zip (Extend ℓ τ1 r1) (Extend ℓ τ2 r2))
zipExtendSwap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Map preserves uniqueness of labels.
uniqueMap :: forall r f. Dict (AllUniqueLabels (Map f r) ≈ AllUniqueLabels r)
uniqueMap = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Ap preserves uniqueness of labels.
uniqueAp :: forall r fs. Dict (AllUniqueLabels (Ap fs r) ≈ AllUniqueLabels r)
uniqueAp = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | ApSingle preserves uniqueness of labels.
uniqueApSingle :: forall r x. Dict (AllUniqueLabels (ApSingle r x) ≈ AllUniqueLabels r)
uniqueApSingle = UNSAFE.unsafeCoerce $ Dict @Unconstrained

-- | Zip preserves uniqueness of labels.
uniqueZip :: forall r1 r2. Dict (AllUniqueLabels (Zip r1 r2) ≈ (AllUniqueLabels r1, AllUniqueLabels r2))
uniqueZip = UNSAFE.unsafeCoerce $ Dict @Unconstrained
