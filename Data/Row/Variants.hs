-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Row.Variants
--
-- This module implements extensible variants using closed type families.
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
  , Extendable(..), Extend, type (.\), Lacks, diversify, type (.+)
  -- ** Modification
  , Updatable(..), Focusable(..), Modify, Renamable(..), Rename
  -- * Destruction
  , impossible, trial, trial', multiTrial, viewV
  -- ** Types for destruction
  , type (.!), type (.-), type (.\\), type (.==)
  -- * Row operations
  -- ** Map
  , Map, vmapc, vmap, vxformc, vxform
  -- ** Fold
  , Forall(..), Erasable(..), Unconstrained1
  -- ** Sequence
  , vsequence
  -- ** labels
  , labels
  )
where

import Control.Applicative
import Control.Arrow (left, right)
import Control.DeepSeq (NFData(..), deepseq)

import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Maybe (fromMaybe)
import Data.Proxy
import Data.String (IsString)
import Data.Text (Text)

import GHC.TypeLits

import Unsafe.Coerce

import Data.Row.Internal

{--------------------------------------------------------------------
  Polymorphic Variants
--------------------------------------------------------------------}

-- | The variant type.
data Var (r :: Row *) where
  OneOf :: Text -> HideType -> Var r

instance Forall r Show => Show (Var r) where
  show v = (\ (x, y) -> "{" ++ x ++ "=" ++ y ++ "}") $ eraseWithLabels (Proxy @Show) show v

instance Forall r Eq => Eq (Var r) where
  r == r' = fromMaybe False $ eraseZip (Proxy @Eq) (==) r r'

instance (Eq (Var r), Forall r Ord) => Ord (Var r) where
  compare :: Var r -> Var r -> Ordering
  compare x y = getConst $ metamorph' @r @Ord @(Product Var Var) @(Const Ordering) @(Const Ordering) Proxy doNil doUncons doCons (Pair x y)
    where doNil (Pair x _) = impossible x
          doUncons l (Pair r1 r2) = case (trial r1 l, trial r2 l) of
            (Left a,  Left b)  -> Left $ Const $ compare a b
            (Left _,  Right _) -> Left $ Const LT
            (Right _, Left _)  -> Left $ Const GT
            (Right x, Right y) -> Right $ Pair x y
          doCons _ (Left (Const c)) = Const c
          doCons _ (Right (Const c)) = Const c

instance Forall r NFData => NFData (Var r) where
  rnf r = getConst $ metamorph' @r @NFData @Var @(Const ()) @Identity Proxy empty doUncons doCons r
    where empty = const $ Const ()
          doUncons l = left Identity . flip trial l
          doCons _ (Left x)  = deepseq x $ Const ()
          doCons _ (Right v) = deepseq v $ Const ()


{--------------------------------------------------------------------
  Basic Operations
--------------------------------------------------------------------}

-- | An unsafe way to make a Variant.  This function does not guarantee that
-- the labels are all unique.
unsafeMakeVar :: forall r l. KnownSymbol l => Label l -> r .! l -> Var r
unsafeMakeVar (toKey -> l) = OneOf l . HideType

-- | A Variant with no options is uninhabited.
impossible :: Var Empty -> a
impossible _ = error "Impossible! Somehow, a variant of nothing was produced."

-- | Create a variant.  The first type argument is the set of types that the Variant
-- lives in.
just :: forall r l. (AllUniqueLabels r, KnownSymbol l) => Label l -> r .! l -> Var r
just = unsafeMakeVar

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
  update (toKey -> l') a (OneOf l x) = OneOf l $ if l == l' then HideType a else x

instance Focusable Var where
  type FRequires Var = Applicative
  -- | If the variant exists at the given label, focus on the value associated with it.
  -- Otherwise, do nothing.
  focus (toKey -> l') f (OneOf l (HideType x)) = if l == l' then (OneOf l . HideType) <$> f (unsafeCoerce x) else pure (OneOf l (HideType x))

instance Renamable Var where
  -- | Rename the given label.
  rename (toKey -> l1) (toKey -> l2) (OneOf l x) = OneOf (if l == l1 then l2 else l) x

-- | Convert a variant into either the value at the given label or a variant without
-- that label.  This is the basic variant destructor.
trial :: KnownSymbol l => Var r -> Label l -> Either (r .! l) (Var (r .- l))
trial (OneOf l (HideType x)) (toKey -> l') = if l == l' then Left (unsafeCoerce x) else Right (OneOf l (HideType x))

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
  eraseWithLabels _ f = getConst . metamorph' @ρ @c @Var @(Const (s,b)) @Identity Proxy impossible doUncons doCons
    where doUncons l = left Identity . flip trial l
          doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => Label ℓ -> Either (Identity τ) (Const (s,b) ('R ρ)) -> Const (s,b) ('R (ℓ :-> τ ': ρ))
          doCons l (Left (Identity x)) = Const (show' l, f x)
          doCons _ (Right (Const c)) = Const c
  eraseZip :: forall ρ c b. Forall ρ c => Proxy c -> (forall a. c a => a -> a -> b) -> Var ρ -> Var ρ -> Maybe b
  eraseZip _ f x y = getConst $ metamorph' @ρ @c @(Product Var Var) @(Const (Maybe b)) @(Const (Maybe b)) Proxy doNil doUncons doCons (Pair x y)
    where doNil _ = Const Nothing
          doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                   => Label ℓ -> Product Var Var ('R (ℓ :-> τ ': ρ)) -> Either (Const (Maybe b) τ) (Product Var Var ('R ρ))
          doUncons l (Pair r1 r2) = case (trial r1 l, trial r2 l) of
            (Left a,  Left b)  -> Left $ Const $ Just $ f a b
            (Right x, Right y) -> Right $ Pair x y
            _ -> Left $ Const Nothing
          doCons _ (Left  (Const c)) = Const c
          doCons _ (Right (Const c)) = Const c


{--------------------------------------------------------------------
  Variant initialization
--------------------------------------------------------------------}

-- | A helper function for unsafely adding an element to the front of a variant
unsafeInjectFront :: forall l a r. KnownSymbol l => Var (R r) -> Var (R (l :-> a ': r))
unsafeInjectFront = unsafeCoerce

-- | Initialize a variant from a producer function over labels.
--   This function works over an 'Alternative'.
vinitAWithLabel :: forall c f ρ. (Alternative f, Forall ρ c, AllUniqueLabels ρ)
                => (forall l a. (KnownSymbol l, c a) => Label l -> f a) -> f (Var ρ)
vinitAWithLabel mk = getCompose $ metamorph @ρ @c @(Const ()) @(Compose f Var) @(Const ()) Proxy doNil doUncons doCons (Const ())
  where doNil _ = Compose $ empty
        doUncons _ _ = (Const (), Const ())
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => Label ℓ -> Const () τ -> Compose f Var ('R ρ) -> Compose f Var ('R (ℓ :-> τ ': ρ))
        doCons l _ (Compose v) = Compose $
          (unsafeMakeVar l <$> mk @ℓ @τ Label) <|> (unsafeInjectFront <$> v)

-- | VMap is used internally as a type level lambda for defining variant maps.
newtype VMap (f :: * -> *) (ρ :: Row *) = VMap { unVMap :: Var (Map f ρ) }

-- | A function to map over a variant given a constraint.
vmapc :: forall c f r. Forall r c => (forall a. c a => a -> f a) -> Var r -> Var (Map f r)
vmapc f = unVMap . metamorph' @r @c @Var @(VMap f) @Identity Proxy doNil doUncons doCons
  where
    doNil = impossible
    doUncons l = left Identity . flip trial l
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> Either (Identity τ) (VMap f ('R ρ)) -> VMap f ('R (ℓ :-> τ ': ρ))
    doCons l (Left (Identity x)) = VMap $ unsafeMakeVar l $ f x
    doCons _ (Right (VMap v)) = VMap $ unsafeInjectFront v

-- | A function to map over a variant given no constraint.
vmap :: forall f r. Forall r Unconstrained1 => (forall a. a -> f a) -> Var r -> Var (Map f r)
vmap = vmapc @Unconstrained1

-- | A mapping function specifically to convert @f a@ values to @g a@ values.
vxformc :: forall r c f g. Forall r c => (forall a. c a => f a -> g a) -> Var (Map f r) -> Var (Map g r)
vxformc f = unVMap . metamorph' @r @c @(VMap f) @(VMap g) @f Proxy doNil doUncons doCons . VMap
  where
    doNil = impossible . unVMap
    doUncons l = right VMap . flip trial l . unVMap
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> Either (f τ) (VMap g ('R ρ)) -> VMap g ('R (ℓ :-> τ ': ρ))
    doCons l (Left x) = VMap $ unsafeMakeVar l $ f x
    doCons _ (Right (VMap v)) = VMap $ unsafeInjectFront v

-- | A form of @rxformc@ that doesn't have a constraint on @a@
vxform :: forall r f g . Forall r Unconstrained1 => (forall a. f a -> g a) -> Var (Map f r) -> Var (Map g r)
vxform = vxformc @r @Unconstrained1

-- | Applicative sequencing over a variant
vsequence :: forall f r. (Forall r Unconstrained1, Applicative f) => Var (Map f r) -> f (Var r)
vsequence = getCompose . metamorph' @r @Unconstrained1 @(VMap f) @(Compose f Var) @f Proxy doNil doUncons doCons . VMap
  where
    doNil (VMap x) = impossible x
    doUncons l = right VMap . flip trial l . unVMap
    doCons l (Left fx) = Compose $ unsafeMakeVar l <$> fx
    doCons _ (Right (Compose v)) = Compose $ unsafeInjectFront <$> v

