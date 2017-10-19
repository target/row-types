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
  , KnownSymbol
  , Var, Row, Empty
  -- * Construction
  , HasType, just, just'
  -- ** Extension
  , Extendable(..), diversify, (:+)
  -- ** Modification
  , Updatable(..), Focusable(..), Modify, Renamable(..), Rename
  -- ** Syntactic sugar
  , VarOp(..), RowOp(..), (*|), (:|), (:==)
  -- * Destruction
  , impossible, trial, trial', multiTrial, viewV
  -- ** Types for destruction
  , (:!), (:-)
  -- * Folds
  , Erasable(..)
  -- ** labels
  , labels
  )
where

import Data.Functor.Const
import Data.Maybe (fromMaybe, fromJust)
import Data.Proxy
import Data.String (IsString)

import GHC.TypeLits
import GHC.Exts -- needed for constraints kinds

import Unsafe.Coerce

import Data.OpenRecords.Internal.Row

{--------------------------------------------------------------------
  Polymorphic Variants
--------------------------------------------------------------------}

-- | The variant type.
data Var (r :: Row *) where
  OneOf :: (String, HideType) -> Var r

instance Forall r Show => Show (Var r) where
  show v = (\ (x, y) -> "{" ++ x ++ "=" ++ y ++ "}") $ eraseWithLabels (Proxy @Show) show v

instance Forall r Eq => Eq (Var r) where
  r == r' = fromMaybe False $ eraseZip (Proxy @Eq) (==) r r'

type instance ValOf Var τ = Maybe τ


{--------------------------------------------------------------------
  Basic Operations
--------------------------------------------------------------------}

-- | A Variant with no options is uninhabited.
impossible :: Var Empty -> a
impossible _ = error "Impossible! Somehow, a variant of nothing was produced."

-- | Create a variant.  The first type argument is the set of types that the Variant
-- lives in.
just :: forall r l. (AllUniqueLabels r, KnownSymbol l) => Label l -> r :! l -> Var r
just (show -> l) a = OneOf (l, HideType a)

-- | A version of 'just' that creates the variant of only one type.
just' :: KnownSymbol l => Label l -> a -> Var (l ::= a :| Empty)
just' = just

instance Extendable Var where
  type Inp Var a = Proxy a
  -- | Extend the variant with a single type via value-level label and proxy.
  extend _ _ (OneOf (l, x)) = OneOf (l, x)

-- | Make the variant arbitrarily more diverse.
diversify :: forall r' r. AllUniqueLabels (r :+ r') => Var r -> Var (r :+ r')
diversify (OneOf (l, x)) = OneOf (l, x)

instance Updatable Var where
  -- | If the variant exists at the given label, update it to the given value.
  -- Otherwise, do nothing.
  update (show -> l') a (OneOf (l, x)) = OneOf (l, if l == l' then HideType a else x)

instance Focusable Var where
  -- | If the variant exists at the given label, focus on the value associated with it.
  -- Otherwise, do nothing.
  focus (show -> l') f (OneOf (l, HideType x)) = if l == l' then (OneOf . (l,) . HideType) <$> f (unsafeCoerce x) else pure (OneOf (l, HideType x))

instance Renamable Var where
  -- | Rename the given label.
  rename (show -> l1) (show -> l2) (OneOf (l, x)) = OneOf (if l == l1 then l2 else l, x)

-- | Convert a variant into either the value at the given label or a variant without
-- that label.  This is the basic variant destructor.
trial :: KnownSymbol l => Var r -> Label l -> Either (r :! l) (Var (r :- l))
trial (OneOf (l, HideType x)) (show -> l') = if l == l' then Left (unsafeCoerce x) else Right (OneOf (l, HideType x))

-- | A version of 'trial' that ignores the leftover variant.
trial' :: KnownSymbol l => Var r -> Label l -> Maybe (r :! l)
trial' = (either Just (const Nothing) .) . trial

-- | A trial over multiple types
multiTrial :: forall x y. (AllUniqueLabels x, Forall (y :// x) Unconstrained1) => Var y -> Either (Var x) (Var (y :// x))
multiTrial (OneOf (l, x)) = if l `elem` labels @(y :// x) @Unconstrained1 Proxy then Right (OneOf (l, x)) else Left (OneOf (l, x))

-- | A convenient function for using view patterns when dispatching variants.
--   For example:
--
-- @
-- myShow :: Var ("y" '::= String :| "x" '::= Int :| Empty) -> String
-- myShow (viewV x -> Just n) = "Int of "++show n
-- myShow (viewV y -> Just s) = "String of "++s @
viewV :: KnownSymbol l => Label l -> Var r -> Maybe (r :! l)
viewV = flip trial'




-- | Type level datakind corresponding to 'RecOp'.
--   Here we provide a datatype for denoting row operations. Use ':|' to
--   actually apply the type level operation.
--
--   This allows us to chain value level operations with nicer syntax.
--   For example we can write:
--
-- > p :*<-| z *| y :*<- 'b' *| z :*!= Proxy @Bool *| x :*= Proxy @Double *| just' y 'a'
--
-- which is an expression of type:
--
-- > Var ("p" ::= Bool :| "x" ::= Double :| "y" ::= Char :| Empty)
--
-- Without this sugar, we would have written it like this:
--
-- > rename p z $ update y 'b' $ extendUnique z (Proxy @Bool) $ extend x (Proxy @Double) $ just' y 'a'
infix 5 :*=
infix 5 :*<-
data VarOp (c :: Row * -> Constraint) (rowOp :: RowOp *) where
  (:*<-)  :: KnownSymbol l => Label l -> a -> VarOp (HasType l a) RUp
  (:*=)   :: KnownSymbol l => Label l -> Proxy a -> VarOp (Lacks l) (l ::= a)
  (:*<-|) :: (KnownSymbol l, KnownSymbol l', r :\ l') => Label l' -> Label l -> VarOp (Lacks l') (l' ::<-| l)




-- | Apply an operation to a record.
infixr 4 *|
(*|) :: c r => VarOp c ro -> Var r -> Var (ro :| r)
(l  :*<- a)  *| m  = update l a m
(l  :*= a)   *| m  = extend l a m
(l' :*<-| l) *| m  = rename l l' m


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


