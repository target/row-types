-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Variants
--
-- This module implements extensible variants using closed type famillies.
--
-----------------------------------------------------------------------------


module Data.Row.Variants
  (
  -- * Types and constraints
    Label(..)
  , KnownSymbol, AllUniqueLabels
  , Var, Row, Empty
  -- * Construction
  , HasType, just, just'
  , vinitAWithLabel
  -- ** Extension
  , Extendable(..), Extend, type (.\), diversify, type (.+)
  -- ** Modification
  , Updatable(..), Focusable(..), Modify, Renamable(..), Rename
  -- * Destruction
  , impossible, trial, trial', multiTrial, viewV
  , Forall(..), Unconstrained1
  -- ** Types for destruction
  , type (.!), type (.-), type (.\\), type (.==)
  -- * Folds
  , Erasable(..)
  -- ** labels
  , labels
  )
where

import Control.Applicative

import Data.Maybe (fromMaybe, fromJust)
import Data.Proxy
import Data.String (IsString)

import GHC.TypeLits

import Unsafe.Coerce

import Data.Row.Internal

{--------------------------------------------------------------------
  Polymorphic Variants
--------------------------------------------------------------------}

-- | The variant type.
data Var (r :: Row *) where
  OneOf :: String -> HideType -> Var r

instance Forall r Show => Show (Var r) where
  show v = (\ (x, y) -> "{" ++ x ++ "=" ++ y ++ "}") $ eraseWithLabels (Proxy @Show) show v

instance Forall r Eq => Eq (Var r) where
  r == r' = fromMaybe False $ eraseZip (Proxy @Eq) (==) r r'

instance (Eq (Var r), Forall r Ord) => Ord (Var r) where
  compare :: Var r -> Var r -> Ordering
  compare x y = getConst $ metamorph @r @Ord @(RowPair Var) @(Const Ordering) doNil doUncons doCons (RowPair (x,y))
    where doNil = impossible . fst . unRowPair
          doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, Ord τ)
                   => (RowPair Var) ('R (ℓ :-> τ ': ρ)) -> ((Maybe τ, Maybe τ), (RowPair Var) ('R ρ))
          doUncons (RowPair (r1, r2)) = case (trial r1 (Label @ℓ), trial r2 (Label @ℓ)) of
            (Left a,  Left b)  -> ((Just a, Just b),  error "impossible")
            (Left a,  Right _) -> ((Just a, Nothing), error "impossible")
            (Right _, Left b)  -> ((Nothing, Just b), error "impossible")
            (Right x, Right y) -> ((Nothing, Nothing), RowPair (x, y))
          doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, Ord τ)
                 => (Maybe τ, Maybe τ) -> Const Ordering ('R ρ) -> Const Ordering ('R (ℓ :-> τ ': ρ))
          doCons (Just a,  Just b) _ = Const $ compare a b
          doCons (Just _,  Nothing) _ = Const LT
          doCons (Nothing, Just _) _ = Const GT
          doCons (Nothing, Nothing) (Const c) = Const c

type instance ValOf Var τ = Maybe τ


{--------------------------------------------------------------------
  Basic Operations
--------------------------------------------------------------------}

-- | A Variant with no options is uninhabited.
impossible :: Var Empty -> a
impossible _ = error "Impossible! Somehow, a variant of nothing was produced."

-- | Create a variant.  The first type argument is the set of types that the Variant
-- lives in.
just :: forall r l. (AllUniqueLabels r, KnownSymbol l) => Label l -> r .! l -> Var r
just (show -> l) a = OneOf l $ HideType a

-- | A version of 'just' that creates the variant of only one type.
just' :: KnownSymbol l => Label l -> a -> Var (l .== a)
just' = just

instance Extendable Var where
  type Inp Var a = Proxy a
  -- | Extend the variant with a single type via value-level label and proxy.
  extend _ _ = unsafeCoerce --(OneOf l x) = OneOf l x

-- | Make the variant arbitrarily more diverse.
diversify :: forall r' r. AllUniqueLabels (r .+ r') => Var r -> Var (r .+ r')
diversify = unsafeCoerce -- (OneOf l x) = OneOf l x

instance Updatable Var where
  -- | If the variant exists at the given label, update it to the given value.
  -- Otherwise, do nothing.
  update (show -> l') a (OneOf l x) = OneOf l $ if l == l' then HideType a else x

instance Focusable Var where
  -- | If the variant exists at the given label, focus on the value associated with it.
  -- Otherwise, do nothing.
  focus (show -> l') f (OneOf l (HideType x)) = if l == l' then (OneOf l . HideType) <$> f (unsafeCoerce x) else pure (OneOf l (HideType x))

instance Renamable Var where
  -- | Rename the given label.
  rename (show -> l1) (show -> l2) (OneOf l x) = OneOf (if l == l1 then l2 else l) x

-- | Convert a variant into either the value at the given label or a variant without
-- that label.  This is the basic variant destructor.
trial :: KnownSymbol l => Var r -> Label l -> Either (r .! l) (Var (r .- l))
trial (OneOf l (HideType x)) (show -> l') = if l == l' then Left (unsafeCoerce x) else Right (OneOf l (HideType x))

-- | A version of 'trial' that ignores the leftover variant.
trial' :: KnownSymbol l => Var r -> Label l -> Maybe (r .! l)
trial' = (either Just (const Nothing) .) . trial

-- | A trial over multiple types
multiTrial :: forall x y. (AllUniqueLabels x, Forall (y .\\ x) Unconstrained1) => Var y -> Either (Var x) (Var (y .\\ x))
multiTrial (OneOf l x) = if l `elem` labels @(y .\\ x) @Unconstrained1 then Right (OneOf l x) else Left (OneOf l x)

-- | A convenient function for using view patterns when dispatching variants.
--   For example:
--
-- @
-- myShow :: Var ("y" '::= String :| "x" '::= Int :| Empty) -> String
-- myShow (viewV x -> Just n) = "Int of "++show n
-- myShow (viewV y -> Just s) = "String of "++s @
viewV :: KnownSymbol l => Label l -> Var r -> Maybe (r .! l)
viewV = flip trial'




{--------------------------------------------------------------------
  Folds and maps
--------------------------------------------------------------------}
instance Erasable Var where
  type Output Var a = a
  type OutputZip Var a = Maybe a
  erase p f = snd @String . eraseWithLabels p f
  eraseWithLabels :: forall s ρ c b. (Forall ρ c, IsString s) => Proxy c -> (forall a. c a => a -> b) -> Var ρ -> (s,b)
  eraseWithLabels _ f = fromJust . getConst . metamorph @ρ @c @Var @(Const (Maybe (s,b))) impossible doUncons doCons
    where doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                   => Var ('R (ℓ :-> τ ': ρ)) -> (Maybe τ, Var ('R ρ))
          doUncons v = case trial v (Label @ℓ) of
            Left  x  -> (Just x, error "impossible")
            Right v' -> (Nothing, v')
          doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => Maybe τ -> Const (Maybe (s,b)) ('R ρ) -> Const (Maybe (s,b)) ('R (ℓ :-> τ ': ρ))
          doCons (Just x) _ = Const $ Just (show' (Label @ℓ), f x)
          doCons Nothing (Const c) = Const c
  eraseZip :: forall ρ c b. Forall ρ c => Proxy c -> (forall a. c a => a -> a -> b) -> Var ρ -> Var ρ -> Maybe b
  eraseZip _ f x y = getConst $ metamorph @ρ @c @(RowPair Var) @(Const (Maybe b)) doNil doUncons doCons (RowPair (x,y))
    where doNil _ = Const Nothing
          doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                   => (RowPair Var) ('R (ℓ :-> τ ': ρ)) -> ((Maybe τ, Maybe τ), (RowPair Var) ('R ρ))
          doUncons (RowPair (r1, r2)) = case (trial r1 (Label @ℓ), trial r2 (Label @ℓ)) of
            (Left a,  Left b)  -> ((Just a, Just b),  error "impossible")
            (Left a,  Right _) -> ((Just a, Nothing), error "impossible")
            (Right _, Left b)  -> ((Nothing, Just b), error "impossible")
            (Right x, Right y) -> ((Nothing, Nothing), RowPair (x, y))
          doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => (Maybe τ, Maybe τ) -> Const (Maybe b) ('R ρ) -> Const (Maybe b) ('R (ℓ :-> τ ': ρ))
          doCons (Just a,  Just b) _ = Const $ Just $ f a b
          doCons (Just _,  Nothing) _ = Const Nothing
          doCons (Nothing, Just _) _ = Const Nothing
          doCons (Nothing, Nothing) (Const c) = Const c


{--------------------------------------------------------------------
  Variant initialization
--------------------------------------------------------------------}

-- | Initialize a variant from a producer function over labels.
--   This function works over an 'Alternative'.
vinitAWithLabel :: forall c f ρ. (Alternative f, Forall ρ c, AllUniqueLabels ρ)
                => (forall l a. (KnownSymbol l, c a) => Label l -> f a) -> f (Var ρ)
vinitAWithLabel mk = unFRow $ metamorph @ρ @c @(Const ()) @(FRow Var f) doNil doUncons doCons (Const ())
  where doNil :: Const () Empty -> FRow Var f Empty
        doNil _ = FRow $ empty
        doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => Const () ('R (ℓ :-> τ ': ρ)) -> ((), Const () ('R ρ))
        doUncons _ = ((), Const ())
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => () -> FRow Var f ('R ρ) -> FRow Var f ('R (ℓ :-> τ ': ρ))
        doCons _ (FRow v) = FRow $
          ((OneOf (show $ Label @ℓ) . HideType) <$> mk @ℓ @τ Label) <|> (unsafeInjectFront @ℓ @τ <$> v)

-- | A helper function for unsafely adding an element to the front of a record
unsafeInjectFront :: forall l a r. KnownSymbol l => Var (R r) -> Var (R (l :-> a ': r))
unsafeInjectFront = unsafeCoerce

