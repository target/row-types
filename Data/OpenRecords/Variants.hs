-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Variants
--
-- This module implements extensible variants using closed type famillies.
--
-----------------------------------------------------------------------------


module Data.OpenRecords.Variants
  (
  -- * Types and constraints
    Label(..)
  , KnownSymbol(..)
  , Var, Row
  -- * Construction
  , HasType, just, just'
  -- ** Extension
  , extend, Subset, diversify, (:+), (:++)
  -- ** Modification
  , update, focus, Modify, rename, Rename
  -- * Destruction
  , impossible, trial, trial', multiTrial, Complement
  , (:!), (:-)
  , Switch(..)
  -- * labels
  , labels
  )
where

import Data.Functor.Const
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import Data.Sequence(Seq,viewl,ViewL(..),(><),(<|))
import qualified Data.HashMap.Lazy as M
import qualified Data.Sequence as S
import Unsafe.Coerce
import Data.List
import Data.Maybe (fromMaybe)
import Data.String (IsString (fromString))
import GHC.TypeLits
import GHC.Exts -- needed for constraints kinds
import Data.Proxy
import Data.Type.Equality (type (==))
import Unconstrained

import Data.OpenRecords.Internal.Row

{--------------------------------------------------------------------
  Polymorphic Variants
--------------------------------------------------------------------}

-- | A Variant with no options is uninhabited.
-- impossible :: Var Empty -> a
-- impossible _ = error "Impossible! Somehow, a variant of nothing was produced."

-- | Create a variant.  The first type argument is the set of types that the Variant
-- lives in.
just :: forall r l a. (HasType l a r, KnownSymbol l) => Label l -> a -> Var r
just (show -> l) a = OneOf (l, HideType a)

-- | A version of 'just' that creates the variant of only one type.
just' :: KnownSymbol l => Label l -> a -> Var (Extend l a Empty)
just' = just

-- | Extend the variant with a single type via value-level label and proxy.
-- extendV :: forall l a r. KnownSymbol l => Label l -> Proxy a -> Var r -> Var (Extend l a r)
-- extendV _ _ (OneOf (l, x)) = OneOf (l, x)

-- | Make the variant arbitrarily more diverse.
diversify :: forall r' r. Subset r r' => Var r -> Var r'
diversify (OneOf (l, x)) = OneOf (l, x)

-- | If the variant exists at the given label, update it to the given value.
-- Otherwise, do nothing.
-- updateV :: KnownSymbol l => Label l -> r :! l -> Var r -> Var r
-- updateV (show -> l') a (OneOf (l, x)) = OneOf (l, if l == l' then HideType a else x)

-- | If the variant exists at the given label, focus on the value associated with it.
-- Otherwise, do nothing.
-- focusV :: (Applicative f, KnownSymbol l) => Label l -> (r :! l -> f a) -> Var r -> f (Var (Modify l a r))
-- focusV (show -> l') f (OneOf (l, HideType x)) = if l == l' then (OneOf . (l,) . HideType) <$> f (unsafeCoerce x) else pure (OneOf (l, HideType x))

-- | Rename the given label.
-- renameV :: (KnownSymbol l, KnownSymbol l') => Label l -> Label l' -> Var r -> Var (Rename l l' r)
-- renameV (show -> l1) (show -> l2) (OneOf (l, x)) = OneOf (if l == l1 then l2 else l, x)

-- | Convert a variant into either the value at the given label or a variant without
-- that label.  This is the basic variant destructor.
-- trial :: KnownSymbol l => Var r -> Label l -> Either (r :! l) (Var (r :- l))
-- trial (OneOf (l, HideType x)) (show -> l') = if l == l' then Left (unsafeCoerce x) else Right (OneOf (l, HideType x))

-- | A version of 'trial' that ignores the leftover variant.
trial' :: KnownSymbol l => Var r -> Label l -> Maybe (r :! l)
trial' = (either Just (const Nothing) .) . trial

-- | A trial over multiple types
multiTrial :: forall y x. Forall y Unconstrained1 => Var x -> Either (Var y) (Var (Complement x y))
multiTrial (OneOf (l, x)) = if l `elem` labels (Proxy @y) then Left (OneOf (l, x)) else Right (OneOf (l, x))


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

