{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
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
  , KnownSymbol, AllUniqueLabels, WellBehaved
  , Var, Row, Empty, type (≈)
  -- * Construction
  , HasType, pattern IsJust, singleton, unSingleton
  , fromLabels, fromLabelsMap
  -- ** Extension
  , type (.\), Lacks, type (.\/), diversify, extend, type (.+)
  -- ** Modification
  , update, focus, Modify, rename, Rename
  -- * Destruction
  , impossible, trial, trial', multiTrial, view
  , restrict, split
  -- ** Types for destruction
  , type (.!), type (.-), type (.\\), type (.==)
  -- * Native Conversion
  -- $native
  , toNative, fromNative, fromNativeGeneral
  , ToNative, FromNative, FromNativeGeneral
  , NativeRow
  -- * Row operations
  -- ** Map
  , Map, map, map', transform, transform'
  -- ** Fold
  , Forall, erase, eraseWithLabels, eraseZipGeneral, eraseZip
  -- ** Applicative-like functions
  , traverse, traverseMap
  , sequence
  -- ** Compose
  -- $compose
  , compose, uncompose
  -- ** labels
  , labels
  -- ** ApSingle functions
  , eraseSingle, mapSingle, eraseZipSingle
  -- ** Coerce
  , coerceVar
  )
where

import Prelude hiding (map, sequence, traverse, zip)

import Control.Applicative
import Control.DeepSeq     (NFData(..), deepseq)

import Data.Bifunctor (Bifunctor(..))
import Data.Coerce
import Data.Constraint                (Constraint)
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Generics.Sum.Constructors (AsConstructor(..), AsConstructor'(..))
import Data.Maybe                     (fromMaybe)
import Data.Profunctor                (Choice(..), Profunctor(..))
import Data.Proxy
import Data.String                    (IsString)
import Data.Text                      (Text)

import qualified GHC.Generics as G
import           GHC.TypeLits

import Unsafe.Coerce

import Data.Row.Dictionaries
import Data.Row.Internal

{--------------------------------------------------------------------
  Polymorphic Variants
--------------------------------------------------------------------}

-- | The variant type.
data Var (r :: Row *) where
  OneOf :: Text -> HideType -> Var r

instance Forall r Show => Show (Var r) where
  show v = (\ (x, y) -> "{" ++ x ++ "=" ++ y ++ "}") $ eraseWithLabels @Show show v

instance Forall r Eq => Eq (Var r) where
  r == r' = fromMaybe False $ eraseZip @Eq (==) r r'

instance (Forall r Eq, Forall r Ord) => Ord (Var r) where
  compare :: Var r -> Var r -> Ordering
  compare = eraseZipGeneral @Ord @r @Ordering @Text $ \case
    (Left (_, x, y))           -> compare x y
    (Right ((s1, _), (s2, _))) -> compare s1 s2

instance Forall r NFData => NFData (Var r) where
  rnf r = getConst $ metamorph @_ @r @NFData @Either @Var @(Const ()) @Identity Proxy empty doUncons doCons r
    where empty = const $ Const ()
          doUncons l = second Identity . flip trial l
          doCons _ x = deepseq x $ Const ()


{--------------------------------------------------------------------
  Basic Operations
--------------------------------------------------------------------}

-- | A Variant with no options is uninhabited.
impossible :: Var Empty -> a
impossible _ = error "Impossible! Somehow, a variant of nothing was produced."

-- | A quick constructor to create a singleton variant.
singleton :: KnownSymbol l => Label l -> a -> Var (l .== a)
singleton = IsJust

-- | A quick destructor for singleton variants.
unSingleton :: forall l a. KnownSymbol l => Var (l .== a) -> (Label l, a)
unSingleton (OneOf _ (HideType x)) = (l, unsafeCoerce x) where l = Label @l

-- | A pattern for variants; can be used to both destruct a variant
-- when in a pattern position or construct one in an expression position.
pattern IsJust :: forall l r. (AllUniqueLabels r, KnownSymbol l) => Label l -> r .! l -> Var r
pattern IsJust l a <- (isJustHelper @l -> (l, Just a)) where
        IsJust (toKey -> l) = OneOf l . HideType

isJustHelper :: forall l r. KnownSymbol l => Var r -> (Label l, Maybe (r .! l))
isJustHelper v = (l, view l v) where l = Label @l

-- | Make the variant arbitrarily more diverse.
diversify :: forall r' r. Var r -> Var (r .\/ r')
diversify = unsafeCoerce -- (OneOf l x) = OneOf l x

-- | A weaker version of 'diversify', but it's helpful for 'metamorph' as it explicitly
-- uses 'Extend'.
extend :: forall a l r. KnownSymbol l => Label l -> Var r -> Var (Extend l a r)
extend _ = unsafeCoerce

-- | If the variant exists at the given label, update it to the given value.
-- Otherwise, do nothing.
update :: (KnownSymbol l, r .! l ≈ a) => Label l -> a -> Var r -> Var r
update (toKey -> l') a (OneOf l x) = OneOf l $ if l == l' then HideType a else x

-- | If the variant exists at the given label, focus on the value associated with it.
-- Otherwise, do nothing.
focus :: forall l r r' a b p f.
  ( AllUniqueLabels r
  , AllUniqueLabels r'
  , KnownSymbol l
  , r  .! l ≈ a
  , r' .! l ≈ b
  , r' ≈ (r .- l) .\/ (l .== b)
  , Applicative f
  , Choice p
  ) => Label l -> p a (f b) -> p (Var r) (f (Var r'))
focus (toKey -> l) =
  dimap unwrap rewrap . left'
  where
    unwrap :: Var r -> Either a (Var r')
    unwrap (OneOf l' (HideType x))
      | l == l'   = Left (unsafeCoerce x)
      | otherwise = Right (OneOf l' (HideType x))
    rewrap :: Either (f b) (Var r') -> f (Var r')
    rewrap = either (fmap $ OneOf l . HideType) pure

-- | Rename the given label.
rename :: (KnownSymbol l, KnownSymbol l') => Label l -> Label l' -> Var r -> Var (Rename l l' r)
rename (toKey -> l1) (toKey -> l2) (OneOf l x) = OneOf (if l == l1 then l2 else l) x

-- | Convert a variant into either the value at the given label or a variant without
-- that label.  This is the basic variant destructor.
trial :: KnownSymbol l => Var r -> Label l -> Either (Var (r .- l)) (r .! l)
trial (OneOf l (HideType x)) (toKey -> l') = if l == l' then Right (unsafeCoerce x) else Left (OneOf l (HideType x))

-- | A version of 'trial' that ignores the leftover variant.
trial' :: KnownSymbol l => Var r -> Label l -> Maybe (r .! l)
trial' = (either (const Nothing) Just .) . trial

-- | A trial over multiple types
multiTrial :: forall x y. (AllUniqueLabels x, Forall (y .\\ x) Unconstrained1) => Var y -> Either (Var (y .\\ x)) (Var x)
multiTrial (OneOf l x) = if l `elem` labels @(y .\\ x) @Unconstrained1 then Left (OneOf l x) else Right (OneOf l x)

-- | A convenient function for using view patterns when dispatching variants.
--   For example:
--
-- @
-- myShow :: Var ("y" '::= String :| "x" '::= Int :| Empty) -> String
-- myShow (view x -> Just n) = "Int of "++show n
-- myShow (view y -> Just s) = "String of "++s @
view :: KnownSymbol l => Label l -> Var r -> Maybe (r .! l)
view = flip trial'

-- | Split a variant into two sub-variants.
split :: forall s r. (WellBehaved s, Subset s r) => Var r -> Either (Var (r .\\ s)) (Var s)
split (OneOf l a) | l `elem` labels @s @Unconstrained1 = Right $ OneOf l a
                  | otherwise                          = Left  $ OneOf l a

-- | Arbitrary variant restriction.  Turn a variant into a subset of itself.
restrict :: forall r r'. (WellBehaved r, Subset r r') => Var r' -> Maybe (Var r)
restrict = either (pure Nothing) Just . split


{--------------------------------------------------------------------
  Folds and maps
--------------------------------------------------------------------}

-- | A standard fold
erase :: forall c ρ b. Forall ρ c => (forall a. c a => a -> b) -> Var ρ -> b
erase f = snd @String . eraseWithLabels @c f

-- | A fold with labels
eraseWithLabels :: forall c ρ s b. (Forall ρ c, IsString s) => (forall a. c a => a -> b) -> Var ρ -> (s,b)
eraseWithLabels f = getConst . metamorph @_ @ρ @c @Either @Var @(Const (s,b)) @Identity Proxy impossible doUncons doCons
  where doUncons l = second Identity . flip trial l
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => Label ℓ -> Either (Const (s,b) ρ) (Identity τ) -> Const (s,b) (Extend ℓ τ ρ)
        doCons _ (Left  (Const c)) = Const c
        doCons l (Right (Identity x)) = Const (show' l, f x)


data ErasedVal c s = forall y. c y => ErasedVal (s, y)
data ErasePair c s ρ = ErasePair (Either (ErasedVal c s) (Var ρ)) (Either (ErasedVal c s) (Var ρ))

-- | A fold over two variants at once.  A call @eraseZipGeneral f x y@ will return
-- @f (Left (show l, a, b))@ when 'x' and 'y' both have values at the same label 'l'
-- and will return @f (Right ((show l1, a), (show l2, b)))@ when they have values
-- at different labels 'l1' and 'l2' respectively.
eraseZipGeneral
  :: forall c ρ b s. (Forall ρ c, IsString s)
  => (forall x y. (c x, c y) => Either (s, x, x) ((s, x), (s, y)) -> b)
  -> Var ρ -> Var ρ -> b
eraseZipGeneral f x y = getConst $ metamorph @_ @ρ @c @Either @(ErasePair c s) @(Const b) @(Const b) Proxy doNil doUncons doCons (ErasePair (Right x) (Right y))
  where
    doNil (ErasePair (Left (ErasedVal a)) (Left (ErasedVal b))) =
      Const $ f $ Right (a, b)
    doNil (ErasePair (Right x) _) = impossible x
    doNil (ErasePair _ (Right y)) = impossible y
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
             => Label ℓ -> ErasePair c s ρ -> Either (ErasePair c s (ρ .- ℓ)) (Const b τ)
    doUncons _ (ErasePair (Left (ErasedVal a)) (Left (ErasedVal b))) =
      Right $ Const $ f $ Right (a, b)
    doUncons l (ErasePair (Right x) (Left eb)) = case (trial x l, eb) of
      (Right a, ErasedVal b) -> Right $ Const $ f $ Right ((show' l, a), b)
      (Left x', _)           -> Left $ ErasePair (Right x') (Left eb)
    doUncons l (ErasePair (Left ea) (Right y)) = case (ea, trial y l) of
      (ErasedVal a, Right b) -> Right $ Const $ f $ Right (a, (show' l, b))
      (_, Left x')           -> Left $ ErasePair (Left ea) (Right x')
    doUncons l (ErasePair (Right x) (Right y)) = case (trial x l, trial y l) of
      (Right (a :: x), Right b) -> Right $ Const $ f @x @x $ Left (show' l, a, b)
      (Right a,        Left y') -> Left $ ErasePair (Left $ ErasedVal (show' l, a)) (Right y')
      (Left x', Right b)        -> Left $ ErasePair (Right x') (Left $ ErasedVal (show' l, b))
      (Left x', Left y')        -> Left $ ErasePair (Right x') (Right y')
    doCons _ (Left  (Const b)) = Const b
    doCons _ (Right (Const b)) = Const b


-- | A simpler fold over two variants at once
eraseZip :: forall c ρ b. Forall ρ c => (forall a. c a => a -> a -> b) -> Var ρ -> Var ρ -> Maybe b
eraseZip f = eraseZipGeneral @c @ρ @(Maybe b) @Text $ \case
    Left (_,x,y) -> Just (f x y)
    _            -> Nothing


-- | VMap is used internally as a type level lambda for defining variant maps.
newtype VMap (f :: * -> *) (ρ :: Row *) = VMap { unVMap :: Var (Map f ρ) }
newtype VMap2 (f :: * -> *) (g :: * -> *) (ρ :: Row *) = VMap2 { unVMap2 :: Var (Map f (Map g ρ)) }

-- | A function to map over a variant given a constraint.
map :: forall c f r. Forall r c => (forall a. c a => a -> f a) -> Var r -> Var (Map f r)
map f = unVMap . metamorph @_ @r @c @Either @Var @(VMap f) @Identity Proxy impossible doUncons doCons
  where
    doUncons l = second Identity . flip trial l
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, AllUniqueLabels (Extend ℓ τ ρ))
           => Label ℓ -> Either (VMap f ρ) (Identity τ) -> VMap f (Extend ℓ τ ρ)
    doCons l (Left (VMap v)) = VMap $ extend @(f τ) l v
      \\ mapExtendSwap @f @ℓ @τ @ρ
    doCons l (Right (Identity x)) = VMap $ IsJust l (f x)
      \\ mapExtendSwap @f @ℓ @τ @ρ
      \\ extendHas @ℓ @(f τ) @(Map f ρ)
      \\ uniqueMap @f @(Extend ℓ τ ρ)

-- | A function to map over a variant given no constraint.
map' :: forall f r. FreeForall r => (forall a. a -> f a) -> Var r -> Var (Map f r)
map' = map @Unconstrained1

-- | Lifts a natrual transformation over a variant.  In other words, it acts as a
-- variant transformer to convert a variant of @f a@ values to a variant of @g a@
-- values.  If no constraint is needed, instantiate the first type argument with
-- 'Unconstrained1'.
transform :: forall c r (f :: * -> *) (g :: * -> *). Forall r c => (forall a. c a => f a -> g a) -> Var (Map f r) -> Var (Map g r)
transform f = unVMap . metamorph @_ @r @c @Either @(VMap f) @(VMap g) @f Proxy doNil doUncons doCons . VMap
  where
    doNil = impossible . unVMap
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
             => Label ℓ -> VMap f ρ -> Either (VMap f (ρ .- ℓ)) (f τ)
    doUncons l = first VMap . flip trial l . unVMap
      \\ mapHas @f @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, AllUniqueLabels (Extend ℓ τ ρ))
           => Label ℓ -> Either (VMap g ρ) (f τ) -> VMap g (Extend ℓ τ ρ)
    doCons l (Left (VMap v)) = VMap $ extend @(g τ) l v
      \\ mapExtendSwap @g @ℓ @τ @ρ
    doCons l (Right x) = VMap $ IsJust l (f x)
      \\ mapExtendSwap @g @ℓ @τ @ρ
      \\ extendHas @ℓ @(g τ) @(Map g ρ)
      \\ uniqueMap @g @(Extend ℓ τ ρ)

-- | A form of @transformC@ that doesn't have a constraint on @a@
transform' :: forall r (f :: * -> *) (g :: * -> *) . FreeForall r => (forall a. f a -> g a) -> Var (Map f r) -> Var (Map g r)
transform' = transform @Unconstrained1 @r

-- | Traverse a function over a variant.
traverse :: forall c f r. (Forall r c, Applicative f) => (forall a. c a => a -> f a) -> Var r -> f (Var r)
traverse f = sequence' @f @r @c . map @c @f @r f

-- | Traverse a function over a Mapped variant.
traverseMap :: forall c (f :: * -> *) (g :: * -> *) (h :: * -> *) r.
  (Forall r c, Applicative f) => (forall a. c a => g a -> f (h a)) -> Var (Map g r) -> f (Var (Map h r))
traverseMap f =
  sequence' @f @(Map h r) @(IsA c h) .
  uncompose' @c @f @h @r .
  transform @c @r @g @(Compose f h) (Compose . f)
  \\ mapForall @h @r @c

-- | Applicative sequencing over a variant with arbitrary constraint.
sequence' :: forall f r c. (Forall r c, Applicative f) => Var (Map f r) -> f (Var r)
sequence' = getCompose . metamorph @_ @r @c @Either @(VMap f) @(Compose f Var) @f Proxy doNil doUncons doCons . VMap
  where
    doNil = impossible . unVMap
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, HasType ℓ τ ρ)
             => Label ℓ -> VMap f ρ -> Either (VMap f (ρ .- ℓ)) (f τ)
    doUncons l = first VMap . flip trial l . unVMap
      \\ mapHas @f @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, AllUniqueLabels (Extend ℓ τ ρ))
           => Label ℓ -> Either (Compose f Var ρ) (f τ) -> Compose f Var (Extend ℓ τ ρ)
    doCons l (Left (Compose v)) = Compose $ extend @τ l <$> v
    doCons l (Right fx) = Compose $ IsJust l <$> fx
      \\ extendHas @ℓ @τ @ρ


-- | Applicative sequencing over a variant
sequence :: forall f r. (FreeForall r, Applicative f) => Var (Map f r) -> f (Var r)
sequence = sequence' @f @r @Unconstrained1

-- $compose
-- We can easily convert between mapping two functors over the types of a row
-- and mapping the composition of the two functors.  The following two functions
-- perform this composition with the gaurantee that:
--
-- >>> compose . uncompose = id
--
-- >>> uncompose . compose = id

-- | Convert from a variant where two functors have been mapped over the types to
-- one where the composition of the two functors is mapped over the types.
compose :: forall (f :: * -> *) (g :: * -> *) r . FreeForall r => Var (Map f (Map g r)) -> Var (Map (Compose f g) r)
compose = unVMap . metamorph @_ @r @Unconstrained1 @Either @(VMap2 f g) @(VMap (Compose f g)) @(Compose f g) Proxy doNil doUncons doCons . VMap2
  where
    doNil = impossible . unVMap2
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, HasType ℓ τ ρ)
             => Label ℓ -> VMap2 f g ρ -> Either (VMap2 f g (ρ .- ℓ)) (Compose f g τ)
    doUncons l = bimap VMap2 Compose . flip trial l . unVMap2
      \\ mapHas @f @ℓ @(g τ) @(Map g ρ)
      \\ mapHas @g @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, AllUniqueLabels (Extend ℓ τ ρ))
           => Label ℓ -> Either (VMap (Compose f g) ρ) (Compose f g τ) -> VMap (Compose f g) (Extend ℓ τ ρ)
    doCons l (Left (VMap v)) = VMap $ extend @(Compose f g τ) l v
      \\ mapExtendSwap @(Compose f g) @ℓ @τ @ρ
    doCons l (Right x) = VMap $ IsJust l x
      \\ mapExtendSwap @(Compose f g) @ℓ @τ @ρ
      \\ extendHas @ℓ @((Compose f g) τ) @(Map (Compose f g) ρ)
      \\ uniqueMap @(Compose f g) @(Extend ℓ τ ρ)

-- | A version of 'uncompose' that allows an arbitrary constraint.
uncompose' :: forall c (f :: * -> *) (g :: * -> *) r . Forall r c => Var (Map (Compose f g) r) -> Var (Map f (Map g r))
uncompose' = unVMap2 . metamorph @_ @r @c @Either @(VMap (Compose f g)) @(VMap2 f g) @(Compose f g) Proxy doNil doUncons doCons . VMap
  where
    doNil = impossible . unVMap
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, HasType ℓ τ ρ)
             => Label ℓ -> VMap (Compose f g) ρ -> Either (VMap (Compose f g) (ρ .- ℓ)) (Compose f g τ)
    doUncons l = first VMap . flip trial l . unVMap
      \\ mapHas @(Compose f g) @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, AllUniqueLabels (Extend ℓ τ ρ))
           => Label ℓ -> Either (VMap2 f g ρ) (Compose f g τ) -> VMap2 f g (Extend ℓ τ ρ)
    doCons l (Left (VMap2 v)) = VMap2 $ extend @(f (g τ)) l v
      \\ mapExtendSwap @f @ℓ @(g τ) @(Map g ρ)
      \\ mapExtendSwap @g @ℓ @τ @ρ
    doCons l (Right (Compose x)) = VMap2 $ IsJust l x
      \\ mapExtendSwap @f @ℓ @(g τ) @(Map g ρ)
      \\ mapExtendSwap @g @ℓ @τ @ρ
      \\ extendHas @ℓ @(f (g τ)) @(Map f (Map g ρ))
      \\ uniqueMap @f @(Extend ℓ (g τ) (Map g ρ))
      \\ uniqueMap @g @(Extend ℓ τ ρ)

-- | Convert from a variant where the composition of two functors have been mapped
-- over the types to one where the two functors are mapped individually one at a
-- time over the types.
uncompose :: forall (f :: * -> *) (g :: * -> *) r . FreeForall r => Var (Map (Compose f g) r) -> Var (Map f (Map g r))
uncompose = uncompose' @Unconstrained1 @f @g @r

-- | Coerce a variant to a coercible representation.  The 'BiForall' in the context
-- indicates that the type of any option in @r1@ can be coerced to the type of
-- the corresponding option in @r2@.
--
-- Internally, this is implemented just with `unsafeCoerce`, but we provide the
-- following implementation as a proof:
--
-- > newtype ConstV a b = ConstV { unConstV :: Var a }
-- > newtype ConstV a b = FlipConstV { unFlipConstV :: Var b }
-- > coerceVar :: forall r1 r2. BiForall r1 r2 Coercible => Var r1 -> Var r2
-- > coerceVar = unFlipConstV . biMetamorph @_ @_ @r1 @r2 @Coercible @Either @ConstV @FlipConstV @Const Proxy doNil doUncons doCons . ConstV
-- >   where
-- >     doNil = impossible . unConstV
-- >     doUncons l = bimap ConstV Const . flip trial l . unConstV
-- >     doCons :: forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, Coercible τ1 τ2, AllUniqueLabels (Extend ℓ τ2 ρ2))
-- >            => Label ℓ -> Either (FlipConstV ρ1 ρ2) (Const τ1 τ2)
-- >            -> FlipConstV (Extend ℓ τ1 ρ1) (Extend ℓ τ2 ρ2)
-- >     doCons l (Left (FlipConstV v)) = FlipConstV $ extend @τ2 l v
-- >     doCons l (Right (Const x)) = FlipConstV $ IsJust l (coerce @τ1 @τ2 x)
-- >       \\ extendHas @ρ2 @ℓ @τ2
coerceVar :: forall r1 r2. BiForall r1 r2 Coercible => Var r1 -> Var r2
coerceVar = unsafeCoerce

{--------------------------------------------------------------------
  Variant initialization
--------------------------------------------------------------------}

-- | Initialize a variant from a producer function that accepts labels.  If this
-- function returns more than one possibility, then one is chosen arbitrarily to
-- be the value in the variant.
fromLabels :: forall c ρ f. (Alternative f, Forall ρ c, AllUniqueLabels ρ)
           => (forall l a. (KnownSymbol l, c a) => Label l -> f a) -> f (Var ρ)
fromLabels mk = getCompose $ metamorph @_ @ρ @c @Const @(Const ()) @(Compose f Var) @Proxy
                                        Proxy doNil doUncons doCons (Const ())
  where doNil _ = Compose $ empty
        doUncons _ _ = Const $ Const ()
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, AllUniqueLabels (Extend ℓ τ ρ))
               => Label ℓ -> Const (Compose f Var ρ) (Proxy τ) -> Compose f Var (Extend ℓ τ ρ)
        doCons l (Const (Compose v)) = Compose $ IsJust l <$> mk l <|> extend @τ l <$> v
          \\ extendHas @ℓ @τ @ρ

-- | Initialize a variant over a `Map`.
fromLabelsMap :: forall c f g ρ. (Alternative f, Forall ρ c, AllUniqueLabels ρ)
              => (forall l a. (KnownSymbol l, c a) => Label l -> f (g a)) -> f (Var (Map g ρ))
fromLabelsMap f = fromLabels @(IsA c g) @(Map g ρ) @f inner
               \\ mapForall @g @ρ @c
               \\ uniqueMap @g @ρ
   where inner :: forall l a. (KnownSymbol l, IsA c g a) => Label l -> f a
         inner l = case as @c @g @a of As -> f l

{--------------------------------------------------------------------
  Functions for variants of ApSingle
--------------------------------------------------------------------}

newtype VApS x (fs :: Row (* -> *)) = VApS { unVApS :: Var (ApSingle fs x) }
newtype FlipApp (x :: *) (f :: * -> *) = FlipApp (f x)

-- | A version of 'erase' that works even when the row-type of the variant argument
-- is of the form @ApSingle fs x@.
eraseSingle
  :: forall (c :: (* -> *) -> Constraint) (fs :: Row (* -> *)) (x :: *) (y :: *)
   . Forall fs c
  => (forall f . (c f) => f x -> y)
  -> Var (ApSingle fs x)
  -> y
eraseSingle f = erase @(ActsOn c x) @(ApSingle fs x) @y g
  \\ apSingleForall @x @fs @c
  where
    g :: forall a. ActsOn c x a => a -> y
    g a = case actsOn @c @x @a of As' -> f a

-- | Performs a functorial-like map over an 'ApSingle' variant.
-- In other words, it acts as a variant transformer to convert a variant of
-- @f x@ values to a variant of @f y@ values.  If no constraint is needed,
-- instantiate the first type argument with 'Unconstrained1'.
mapSingle
  :: forall (c :: (* -> *) -> Constraint) (fs :: Row (* -> *)) (x :: *) (y :: *)
   . (Forall fs c)
  => (forall f . (c f) => f x -> f y)
  -> Var (ApSingle fs x)
  -> Var (ApSingle fs y)
mapSingle f = unVApS . metamorph @_ @fs @c @Either @(VApS x) @(VApS y) @(FlipApp x)
             Proxy doNil doUncons doCons . VApS
 where
  doNil = impossible . unVApS

  doUncons :: forall l f fs
           .  ( c f, fs .! l ≈ f, KnownSymbol l)
           => Label l -> VApS x fs -> Either (VApS x (fs .- l)) (FlipApp x f)
  doUncons l = bimap VApS FlipApp
             . flip (trial \\ apSingleHas @x @l @f @fs) l
             . unVApS

  doCons :: forall l f fs. (KnownSymbol l, c f, AllUniqueLabels (Extend l f fs))
         => Label l
         -> Either (VApS y fs) (FlipApp x f)
         -> VApS y (Extend l f fs)
  doCons l (Right (FlipApp x)) = VApS $ IsJust l (f x)
    \\ apSingleExtendSwap @y @l @f @fs
    \\ extendHas @l @(f y) @(ApSingle fs y)
    \\ uniqueApSingle @y @(Extend l f fs)
  doCons l (Left (VApS v)) = VApS $ extend @(f y) l v
    \\ apSingleExtendSwap @y @l @f @fs

-- | A version of 'eraseZip' that works even when the row-types of the variant
-- arguments are of the form @ApSingle fs x@.
eraseZipSingle :: forall c fs (x :: *) (y :: *) z
                . (Forall fs c)
               => (forall f. c f => f x -> f y -> z)
               -> Var (ApSingle fs x) -> Var (ApSingle fs y) -> Maybe z
eraseZipSingle f x y = getConst $ metamorph @_ @fs @c @Either
    @(Product (VApS x) (VApS y)) @(Const (Maybe z)) @(Const (Maybe z))
    Proxy doNil doUncons doCons (Pair (VApS x) (VApS y))

  where doNil :: Product (VApS x) (VApS y) Empty
              -> Const (Maybe z) (Empty :: Row (* -> *))
        doNil (Pair (VApS z) _) = Const (impossible z)

        doUncons :: forall l f ρ
                  . (KnownSymbol l, c f, ρ .! l ≈ f)
                 => Label l
                 -> Product (VApS x) (VApS y) ρ
                 -> Either (Product (VApS x) (VApS y) (ρ .- l))
                           (Const (Maybe z) f)
        doUncons l (Pair (VApS r1) (VApS r2)) =
          case (
            trial r1 l \\ apSingleHas @x @l @f @ρ,
            trial r2 l \\ apSingleHas @y @l @f @ρ
          ) of
            (Right u, Right v) -> Right $ Const $ Just $ f @f u v
            (Left us, Left vs) -> Left (Pair (VApS us) (VApS vs))
            _                  -> Right $ Const Nothing

        doCons :: forall l (τ :: * -> *) ρ
                . Label l
               -> Either (Const (Maybe z) ρ) (Const (Maybe z) τ)
               -> Const (Maybe z) (Extend l τ ρ)
        doCons _ (Left (Const w))  = Const w
        doCons _ (Right (Const w)) = Const w

{--------------------------------------------------------------------
  Generic instance
--------------------------------------------------------------------}

-- The generic structure we want Vars to have is not the hidden internal one,
-- but rather one that appears as a Haskell sum type.  Thus, we can't derive
-- Generic automatically.
--
-- The following Generic instance creates a representation of a Var that is
-- very similar to a native Haskell sum type except that the tree of possibilities (':+:')
-- that it produces will be extremely unbalanced.  I don't think this is a problem.
-- Furthermore, because we don't want Vars to always have a trailing void option on
-- the end, we must have a special case for singleton Vars, which means that
-- we can't use metamorph.

instance GenericVar r => G.Generic (Var r) where
  type Rep (Var r) =
    G.D1 ('G.MetaData "Var" "Data.Row.Variants" "row-types" 'False) (RepVar r)
  from = G.M1 . fromVar
  to = toVar . G.unM1

class GenericVar r where
  type RepVar (r :: Row *) :: * -> *
  fromVar :: Var r -> RepVar r x
  toVar   :: RepVar r x -> Var r

instance GenericVar Empty where
  type RepVar Empty = G.V1
  fromVar = impossible
  toVar = \case

instance KnownSymbol name => GenericVar (R '[name :-> t]) where
  type RepVar (R (name :-> t ': '[])) = G.C1
    ('G.MetaCons name 'G.PrefixI 'False)
    (G.S1 ('G.MetaSel 'Nothing 'G.NoSourceUnpackedness 'G.NoSourceStrictness 'G.DecidedLazy)
          (G.Rec0 t))
  fromVar (unSingleton -> (_, a)) = G.M1 (G.M1 (G.K1 a))
  toVar (G.M1 (G.M1 (G.K1 a))) = IsJust (Label @name) a

instance
    ( GenericVar (R (name' :-> t' ': r'))
    , KnownSymbol name, Extend name t ('R (name' :-> t' ': r')) ≈ 'R (name :-> t ': (name' :-> t' ': r'))
    , AllUniqueLabels (R (name :-> t ': (name' :-> t' ': r')))
    ) => GenericVar (R (name :-> t ': (name' :-> t' ': r'))) where
  type RepVar (R (name :-> t ': (name' :-> t' ': r'))) = (G.C1
    ('G.MetaCons name 'G.PrefixI 'False)
    (G.S1 ('G.MetaSel 'Nothing 'G.NoSourceUnpackedness 'G.NoSourceStrictness 'G.DecidedLazy)
          (G.Rec0 t)))  G.:+: RepVar (R (name' :-> t' ': r'))
  fromVar v = case trial @name v Label of
    Left v' -> G.R1 (fromVar v')
    Right a -> G.L1 (G.M1 (G.M1 (G.K1 a)))
  toVar (G.L1 (G.M1 (G.M1 (G.K1 a)))) = IsJust (Label @name) a
  toVar (G.R1 g) = extend @t @name @('R (name' :-> t' ': r')) Label $ toVar g

{--------------------------------------------------------------------
  Native data type compatibility
--------------------------------------------------------------------}

-- $native
-- The 'toNative' and 'fromNative' functions allow one to convert between
-- 'Var's and regular Haskell data types ("native" types) that have the same
-- number of constructors such that each constructor has one field and the same
-- name as one of the options of the 'Var', which has the same type as that field.
-- As expected, they compose to form the identity.  Alternatively, one may use
-- 'fromNativeGeneral', which allows a variant with excess options to  still be
-- transformed to a native type.  Because of this, 'fromNativeGeneral' requires a type
-- application (although 'fromNative' does not).  The only requirement is that
-- the native Haskell data type be an instance of 'Generic'.
--
-- For example, consider the following simple data type:
--
-- >>> data Pet = Dog {age :: Int} | Cat {age :: Int} deriving (Generic, Show)
--
-- Then, we have the following:
--
-- >>> toNative $ IsJust (Label @"Dog") 3 :: Pet
-- Dog {age = 3}
-- >>> V.fromNative $ Dog 3 :: Var ("Dog" .== Int .+ "Cat" .== Int)
-- {Dog=3}

type family NativeRow t where
  NativeRow t = NativeRowG (G.Rep t)

type family NativeRowG t where
  NativeRowG (G.M1 G.D m cs) = NativeRowG cs
  NativeRowG G.V1 = Empty
  NativeRowG (l G.:+: r) = NativeRowG l .+ NativeRowG r
  NativeRowG (G.C1 ('G.MetaCons name fixity sels) (G.S1 m (G.Rec0 t))) = name .== t


-- | Conversion helper to bring a variant back into a Haskell type. Note that the
-- native Haskell type must be an instance of 'Generic'.
class ToNativeG a where
  toNative' :: Var (NativeRowG a) -> a x

instance ToNativeG cs => ToNativeG (G.D1 m cs) where
  toNative' = G.M1 . toNative'

instance ToNativeG G.V1 where
  toNative' = impossible

instance (KnownSymbol name)
    => ToNativeG (G.C1 ('G.MetaCons name fixity sels)
                (G.S1 m (G.Rec0 t))) where
  toNative' = G.M1 . G.M1 . G.K1 . snd . unSingleton

instance ( ToNativeG l, ToNativeG r, (NativeRowG l .+ NativeRowG r) .\\ NativeRowG r ≈ NativeRowG l
         , AllUniqueLabels (NativeRowG r), Forall (NativeRowG l) Unconstrained1)
    => ToNativeG (l G.:+: r) where
  toNative' v = case multiTrial @(NativeRowG r) @(NativeRowG (l G.:+: r)) v of
    Left  v' -> G.L1 $ toNative' v'
    Right v' -> G.R1 $ toNative' v'

type ToNative t = (G.Generic t, ToNativeG (G.Rep t))

-- | Convert a variant to a native Haskell type.
toNative :: ToNative t => Var (NativeRow t) -> t
toNative = G.to . toNative'


-- | Conversion helper to turn a Haskell variant into a row-types extensible
-- variant. Note that the native Haskell type must be an instance of 'Generic'.
class FromNativeG a where
  fromNative' :: a x -> Var (NativeRowG a)

instance FromNativeG cs => FromNativeG (G.D1 m cs) where
  fromNative' (G.M1 v) = fromNative' v

instance FromNativeG G.V1 where
  fromNative' = \ case

instance KnownSymbol name
    => FromNativeG (G.C1 ('G.MetaCons name fixity sels)
                       (G.S1 m (G.Rec0 t))) where
  fromNative' (G.M1 (G.M1 (G.K1 x))) = IsJust (Label @name) x

instance (FromNativeG l, FromNativeG r) => FromNativeG (l G.:+: r) where
  -- Ideally, we would use 'diversify' here instead of 'unsafeCoerce', but it
  -- makes the constraints really hairy.
  fromNative' (G.L1 x) = unsafeCoerce $ fromNative' @l x
  fromNative' (G.R1 y) = unsafeCoerce $ fromNative' @r y

type FromNative t = (G.Generic t, FromNativeG (G.Rep t))

-- | Convert a Haskell variant to a row-types Var.
fromNative :: FromNative t => t -> Var (NativeRow t)
fromNative = fromNative' . G.from


-- | Conversion helper to turn a Haskell variant into a row-types extensible
-- variant. Note that the native Haskell type must be an instance of 'Generic'.
class FromNativeGeneralG a ρ where
  fromNativeGeneral' :: a x -> Var ρ

instance FromNativeGeneralG cs ρ => FromNativeGeneralG (G.D1 m cs) ρ where
  fromNativeGeneral' (G.M1 v) = fromNativeGeneral' v

instance FromNativeGeneralG G.V1 ρ where
  fromNativeGeneral' = \ case

instance (KnownSymbol name, ρ .! name ≈ t, AllUniqueLabels ρ)
    => FromNativeGeneralG (G.C1 ('G.MetaCons name fixity sels)
                  (G.S1 m (G.Rec0 t))) ρ where
  fromNativeGeneral' (G.M1 (G.M1 (G.K1 x))) = IsJust (Label @name) x

instance (FromNativeGeneralG l ρ, FromNativeGeneralG r ρ)
    => FromNativeGeneralG (l G.:+: r) ρ where
  -- Ideally, we would use 'diversify' here instead of 'unsafeCoerce', but it
  -- makes the constraints really hairy.
  fromNativeGeneral' (G.L1 x) = unsafeCoerce $ fromNativeGeneral' @l @ρ x
  fromNativeGeneral' (G.R1 y) = unsafeCoerce $ fromNativeGeneral' @r @ρ y

type FromNativeGeneral t ρ = (G.Generic t, FromNativeGeneralG (G.Rep t) ρ)

-- | Convert a Haskell variant to a row-types Var.
fromNativeGeneral :: FromNativeGeneral t ρ => t -> Var ρ
fromNativeGeneral = fromNativeGeneral' . G.from


{--------------------------------------------------------------------
  Generic-lens compatibility
--------------------------------------------------------------------}

-- | Every possibility of a row-types based variant has an 'AsConstructor' instance.
instance {-# OVERLAPPING #-}
  ( AllUniqueLabels r
  , AllUniqueLabels r'
  , KnownSymbol name
  , r  .! name ≈ a
  , r' .! name ≈ b
  , r' ≈ (r .- name) .\/ (name .== b))
  => AsConstructor name (Var r) (Var r') a b where
  _Ctor = focus (Label @name)
  {-# INLINE _Ctor #-}

instance {-# OVERLAPPING #-}
  ( AllUniqueLabels r
  , KnownSymbol name
  , r  .! name ≈ a
  , r ≈ (r .- name) .\/ (name .== a))
  => AsConstructor' name (Var r) a where
  _Ctor' = focus (Label @name)
  {-# INLINE _Ctor' #-}
