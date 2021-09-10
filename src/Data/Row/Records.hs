{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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
-- Module      :  Data.Row.Records
--
-- This module implements extensible records using closed type famillies.
--
-- See Examples.lhs for examples.
--
-- Lists of (label,type) pairs are kept sorted thereby ensuring
-- that { x = 0, y = 0 } and { y = 0, x = 0 } have the same type.
--
-- In this way we can implement standard type classes such as Show, Eq, Ord and Bounded
-- for open records, given that all the elements of the open record satify the constraint.
--
-----------------------------------------------------------------------------


module Data.Row.Records
  (
  -- * Types and constraints
    Label(..)
  , KnownSymbol, AllUniqueLabels, WellBehaved
  , Rec, Row, Empty, type (≈)
  -- * Construction
  , empty
  , type (.==), (.==), pattern (:==), unSingleton
  , default', defaultA
  , fromLabels, fromLabelsA, fromLabelsMapA
  -- ** Extension
  , extend, Extend, Lacks, type (.\)
  -- ** Restriction
  , type (.-), (.-)
  , lazyRemove
  , Subset
  , restrict, split
  -- ** Modification
  , update, focus, multifocus, Modify, rename, Rename
  -- * Query
  , HasType, type (.!), (.!)
  -- * Combine
  -- ** Disjoint union
  , type (.+), (.+), Disjoint, pattern (:+)
  -- ** Overwrite
  , type (.//), (.//)
  -- * Application with functions
  , curryRec
  , (.$)
  -- * Native Conversion
  -- $native
  , fromNative, toNative, toNativeGeneral
  , FromNative, ToNative, ToNativeGeneral
  , NativeRow
  -- * Dynamic Conversion
  , toDynamicMap, fromDynamicMap
  -- * Row operations
  -- ** Map
  , Map, map, map', mapF
  , transform, transform'
  , zipTransform, zipTransform'
  -- ** Fold
  , BiForall, Forall, erase, eraseWithLabels, eraseZip, eraseToHashMap
  -- ** Zip
  , Zip, zip
  -- ** Applicative-like functions
  , traverse, traverseMap
  , sequence, sequence'
  , distribute
  -- ** Compose
  -- $compose
  , compose, uncompose
  , compose', uncompose'
  -- ** Labels
  , labels, labels'
  -- ** Coerce
  , coerceRec
  )
where

import Prelude hiding (map, sequence, traverse, zip)

import Control.DeepSeq (NFData(..), deepseq)

import           Data.Bifunctor               (Bifunctor(..))
import           Data.Coerce
import           Data.Dynamic
import           Data.Functor.Compose
import           Data.Functor.Const
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Generics.Product.Fields (HasField(..), HasField'(..))
import           Data.Hashable
import           Data.HashMap.Lazy            (HashMap)
import qualified Data.HashMap.Lazy            as M
import qualified Data.List                    as L
import           Data.Monoid                  (Endo(..), appEndo)
import           Data.Proxy
import           Data.String                  (IsString)
import           Data.Text                    (Text)

import qualified GHC.Generics as G
import           GHC.TypeLits
import Unsafe.Coerce

import Data.Row.Dictionaries
import Data.Row.Internal


{--------------------------------------------------------------------
  Open records
--------------------------------------------------------------------}
-- | A record with row r.
newtype Rec (r :: Row *) where
  OR :: HashMap Text HideType -> Rec r

instance Forall r Show => Show (Rec r) where
  showsPrec p r =
    case eraseWithLabels @Show (showsPrec 7) r of
      [] ->
        showString "empty"
      xs ->
        showParen
          (p > 6)
          (appEndo $ foldMap Endo (L.intersperse (showString " .+ ") (L.map binds xs)))
    where
      binds (label, value) =
        showChar '#' .
        showString label .
        showString " .== " .
        value

instance Forall r Eq => Eq (Rec r) where
  r == r' = and $ eraseZip @Eq (==) r r'

instance (Forall r Eq, Forall r Ord) => Ord (Rec r) where
  compare m m' = cmp $ eraseZip @Ord compare m m'
      where cmp l | [] <- l' = EQ
                  | a : _ <- l' = a
                  where l' = dropWhile (== EQ) l

instance (Forall r Bounded, AllUniqueLabels r) => Bounded (Rec r) where
  minBound = default' @Bounded minBound
  maxBound = default' @Bounded maxBound

instance Forall r NFData => NFData (Rec r) where
  rnf r = getConst $ metamorph @_ @r @NFData @(,) @Rec @(Const ()) @Identity Proxy empty doUncons doCons r
    where empty = const $ Const ()
          doUncons l = second Identity . lazyUncons l
          doCons _ (r, x) = deepseq x $ deepseq r $ Const ()

-- | The empty record
empty :: Rec Empty
empty = OR M.empty

-- | The singleton record
infix 7 .==
(.==) :: KnownSymbol l => Label l -> a -> Rec (l .== a)
l .== a = extend l a empty

-- | A pattern for the singleton record; can be used to both destruct a record
-- when in a pattern position or construct one in an expression position.
{-# COMPLETE (:==) #-}
infix 7 :==
pattern (:==) :: forall l a. KnownSymbol l => Label l -> a -> Rec (l .== a)
pattern l :== a <- (unSingleton @l @a -> (l, a)) where
        (:==) l a = l .== a

-- | Turns a singleton record into a pair of the label and value.
unSingleton :: forall l a. KnownSymbol l => Rec (l .== a) -> (Label l, a)
unSingleton r = (l, r .! l) where l = Label @l

{--------------------------------------------------------------------
  Basic record operations
--------------------------------------------------------------------}


-- | Record extension. The row may already contain the label,
--   in which case the origin value can be obtained after restriction ('.-') with
--   the label.
extend :: forall a l r. KnownSymbol l => Label l -> a -> Rec r -> Rec (Extend l a r)
extend (toKey -> l) a (OR m) = OR $ M.insert l (HideType a) m

-- | Update the value associated with the label.
update :: (KnownSymbol l, r .! l ≈ a) => Label l -> a -> Rec r -> Rec r
update (toKey -> l) a (OR m) = OR $ M.adjust f l m where f = const (HideType a)

-- | Focus on the value associated with the label.
focus ::
  ( KnownSymbol l
  , r' .! l ≈ b
  , r  .! l ≈ a
  , r' ~ Modify l b r
  , r  ~ Modify l a r'
  , Functor f)
  => Label l -> (a -> f b) -> Rec r -> f (Rec r')
focus (toKey -> l) f (OR m) = case m M.! l of
  HideType x -> OR . flip (M.insert l) m . HideType <$> f (unsafeCoerce x)

-- | Focus on a sub-record
multifocus :: forall u v r f.
  ( Functor f
  , Disjoint u r
  , Disjoint v r)
  => (Rec u -> f (Rec v)) -> Rec (u .+ r) -> f (Rec (v .+ r))
multifocus f (u :+ r) = (.+ r) <$> f u

-- | Rename a label.
rename :: (KnownSymbol l, KnownSymbol l') => Label l -> Label l' -> Rec r -> Rec (Rename l l' r)
rename (toKey -> l) (toKey -> l') (OR m) = OR $ M.insert l' (m M.! l) $ M.delete l m

-- | Record selection
(.!) :: KnownSymbol l => Rec r -> Label l -> r .! l
OR m .! (toKey -> a) = case m M.! a of
  HideType x -> unsafeCoerce x

infixl 6 .-
-- | Record restriction. Remove the label l from the record.
(.-) :: KnownSymbol l => Rec r -> Label l -> Rec (r .- l)
-- OR m .- _ = OR m
OR m .- (toKey -> a) = OR $ M.delete a m

-- | Record disjoint union (commutative)
infixl 6 .+
(.+) :: forall l r. FreeForall l => Rec l -> Rec r -> Rec (l .+ r)
OR l .+ OR r = OR $ M.unionWithKey choose l r
  where
    choose k lv rv = if k `elem` labels' @l @Text then lv else rv

-- | Record overwrite.
--
-- The operation @r .// r'@ creates a new record such that:
--
-- - Any label that is in both @r@ and @r'@ is in the resulting record with the
--   type and value given by the fields in @r@,
--
-- - Any label that is only found in @r@ is in the resulting record.
--
-- - Any label that is only found in @r'@ is in the resulting record.
--
-- This can be thought of as @r@ "overwriting" @r'@.
infixl 6 .//
(.//) :: Rec r -> Rec r' -> Rec (r .// r')
OR l .// OR r = OR $ M.union l r

-- | A pattern version of record union, for use in pattern matching.
{-# COMPLETE (:+) #-}
infixl 6 :+
pattern (:+) :: forall l r. Disjoint l r => Rec l -> Rec r -> Rec (l .+ r)
pattern l :+ r <- (split @l -> (l, r)) where
        (:+) l r = l .+ r

-- | Split a record into two sub-records.
split :: forall s r. (Subset s r, FreeForall s)
         => Rec r -> (Rec s, Rec (r .\\ s))
split (OR m) = (OR $ M.intersection m labelMap, OR $ M.difference m labelMap)
  where
    labelMap = M.fromList $ L.zip (labels' @s) (repeat ())

-- | Arbitrary record restriction.  Turn a record into a subset of itself.
restrict :: forall r r'. (FreeForall r, Subset r r') => Rec r' -> Rec r
restrict = fst . split

-- | Removes a label from the record but does not remove the underlying value.
--
-- This is faster than regular record removal ('.-'), but it has two downsides:
--
-- 1. It may incur a performance penalty during a future merge operation ('.+'), and
--
-- 2. It will keep the reference to the value alive, meaning that it will not get garbage collected.
--
-- Thus, it's great when one knows ahead of time that no future merges will happen
-- and that the whole record will be GC'd soon, for instance, during the catamorphism
-- function of 'metamorph'.
lazyRemove :: KnownSymbol l => Label l -> Rec r -> Rec (r .- l)
lazyRemove _ (OR m) = OR m

-- | This is the same as @(lazyRemove l r, r .! l)@.
lazyUncons :: KnownSymbol l => Label l -> Rec r -> (Rec (r .- l), r .! l)
lazyUncons l r = (lazyRemove l r, r .! l)

-- | Kind of like 'curry' for functions over records.
curryRec :: forall l t r x. KnownSymbol l => Label l -> (Rec (l .== t .+ r) -> x) -> t -> Rec r -> x
curryRec l f t r = f $ (l .== t) .+ r

infixl 2 .$
-- | This function allows one to do partial application on a function of a record.
-- Note that this also means that arguments can be supplied in arbitrary order.
-- For instance, if one had a function like
--
-- > xtheny r = (r .! #x) <> (r .! #y)
--
-- and a record like
--
-- > greeting = #x .== "hello " .+ #y .== "world!"
--
-- Then all of the following would be possible:
--
-- >>> xtheny greeting
-- "hello world!"
--
-- >>> xtheny .$ (#x, greeting) .$ (#y, greeting) $ empty
-- "hello world!"
--
-- >>> xtheny .$ (#y, greeting) .$ (#x, greeting) $ empty
-- "hello world!"
--
-- >>> xtheny .$ (#y, greeting) .$ (#x, #x .== "Goodbye ") $ empty
-- "Goodbye world!"
(.$) :: (KnownSymbol l, r' .! l ≈ t) => (Rec (l .== t .+ r) -> x) -> (Label l, Rec r') -> Rec r -> x
(.$) f (l, r') r = curryRec l f (r' .! l) r

{--------------------------------------------------------------------
  Folds and maps
--------------------------------------------------------------------}
-- An easy type synonym for a pair where both elements are the same type.
newtype Pair' a = Pair' { unPair' :: (a,a) }

-- | A standard fold
erase :: forall c ρ b. Forall ρ c => (forall a. c a => a -> b) -> Rec ρ -> [b]
erase f = fmap (snd @String) . eraseWithLabels @c f

-- | A fold with labels
eraseWithLabels :: forall c ρ s b. (Forall ρ c, IsString s) => (forall a. c a => a -> b) -> Rec ρ -> [(s,b)]
eraseWithLabels f = getConst . metamorph @_ @ρ @c @(,) @Rec @(Const [(s,b)]) @Identity Proxy doNil doUncons doCons
  where doNil _ = Const []
        doUncons l = second Identity . lazyUncons l
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => Label ℓ -> (Const [(s,b)] ρ, Identity τ) -> Const [(s,b)] (Extend ℓ τ ρ)
        doCons l (Const c, Identity x) = Const $ (show' l, f x) : c

-- | A fold over two row type structures at once
eraseZip :: forall c ρ b. Forall ρ c => (forall a. c a => a -> a -> b) -> Rec ρ -> Rec ρ -> [b]
eraseZip f x y = getConst $ metamorph @_ @ρ @c @(,) @(Product Rec Rec) @(Const [b]) @Pair' Proxy (const $ Const []) doUncons doCons (Pair x y)
  where doUncons l (Pair r1 r2) = (Pair r1' r2', Pair' (a, b))
          where (r1', a) = lazyUncons l r1
                (r2', b) = lazyUncons l r2
        doCons :: forall ℓ τ ρ. c τ
               => Label ℓ -> (Const [b] ρ, Pair' τ) -> Const [b] (Extend ℓ τ ρ)
        doCons _ (Const c, unPair' -> x) = Const $ uncurry f x : c

-- | Turns a record into a 'HashMap' from values representing the labels to
--   the values of the record.
eraseToHashMap :: forall c r s b. (IsString s, Eq s, Hashable s, Forall r c) =>
                  (forall a . c a => a -> b) -> Rec r -> HashMap s b
eraseToHashMap f r = M.fromList $ eraseWithLabels @c f r

-- | RMap is used internally as a type level lambda for defining record maps.
newtype RMap f ρ = RMap { unRMap :: Rec (Map f ρ) }
newtype RMap2 f g ρ = RMap2 { unRMap2 :: Rec (Map f (Map g ρ)) }

-- | A function to map over a record given a constraint.
map :: forall c f r. Forall r c => (forall a. c a => a -> f a) -> Rec r -> Rec (Map f r)
map f = unRMap . metamorph @_ @r @c @(,) @Rec @(RMap f) @f Proxy doNil doUncons doCons
  where
    doNil _ = RMap empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
             => Label ℓ -> Rec ρ -> (Rec (ρ .- ℓ), f τ)
    doUncons l = second f . lazyUncons l
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> (RMap f ρ, f τ) -> RMap f (Extend ℓ τ ρ)
    doCons l (RMap r, v) = RMap (extend l v r)
      \\ mapExtendSwap @f @ℓ @τ @ρ

newtype RFMap (g :: k1 -> k2) (ϕ :: Row (k2 -> *)) (ρ :: Row k1) = RFMap { unRFMap :: Rec (Ap ϕ (Map g ρ)) }
newtype RecAp (ϕ :: Row (k -> *)) (ρ :: Row k) = RecAp (Rec (Ap ϕ ρ))
newtype App (f :: k -> *) (a :: k) = App (f a)

-- | A function to map over a Ap record given constraints.
mapF :: forall k c g (ϕ :: Row (k -> *)) (ρ :: Row k). BiForall ϕ ρ c
     => (forall h a. (c h a) => h a -> h (g a))
     -> Rec (Ap ϕ ρ)
     -> Rec (Ap ϕ (Map g ρ))
mapF f = unRFMap . biMetamorph @_ @_ @ϕ @ρ @c @(,) @RecAp @(RFMap g) @App Proxy doNil doUncons doCons . RecAp
  where
    doNil _ = RFMap empty
    doUncons :: forall ℓ f τ ϕ ρ. (KnownSymbol ℓ, c f τ, HasType ℓ f ϕ, HasType ℓ τ ρ)
             => Label ℓ -> RecAp ϕ ρ -> (RecAp (ϕ .- ℓ) (ρ .- ℓ), App f τ)
    doUncons l (RecAp r) = bimap RecAp App $ lazyUncons l r
      \\ apHas @ℓ @f @ϕ @τ @ρ
    doCons :: forall ℓ f τ ϕ ρ. (KnownSymbol ℓ, c f τ)
           => Label ℓ -> (RFMap g ϕ ρ, App f τ) -> RFMap g (Extend ℓ f ϕ) (Extend ℓ τ ρ)
    doCons l (RFMap r, App v) = RFMap (extend l (f @f @τ v) r)
      \\ mapExtendSwap @g @ℓ @τ @ρ
      \\ apExtendSwap @ℓ @f @ϕ @(g τ) @(Map g ρ)

-- | A function to map over a record given no constraint.
map' :: forall f r. FreeForall r => (forall a. a -> f a) -> Rec r -> Rec (Map f r)
map' f = map @Unconstrained1 f

-- | Lifts a natural transformation over a record.  In other words, it acts as a
-- record transformer to convert a record of @f a@ values to a record of @g a@
-- values.  If no constraint is needed, instantiate the first type argument with
-- 'Unconstrained1' or use 'transform''.
transform :: forall c r f g. Forall r c => (forall a. c a => f a -> g a) -> Rec (Map f r) -> Rec (Map g r)
transform f = unRMap . metamorph @_ @r @c @(,) @(RMap f) @(RMap g) @f Proxy doNil doUncons doCons . RMap
  where
    doNil _ = RMap empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
             => Label ℓ -> RMap f ρ -> (RMap f (ρ .- ℓ), f τ)
    doUncons l (RMap r) = first RMap $ lazyUncons l r
      \\ mapHas @f @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> (RMap g ρ, f τ) -> RMap g (Extend ℓ τ ρ)
    doCons l (RMap r, v) = RMap (extend l (f v) r)
      \\ mapExtendSwap @g @ℓ @τ @ρ

-- | A version of 'transform' for when there is no constraint.
transform' :: forall r f g. FreeForall r => (forall a. f a -> g a) -> Rec (Map f r) -> Rec (Map g r)
transform' f = transform @Unconstrained1 @r f


data RecMapPair f g ρ = RecMapPair (Rec (Map f ρ)) (Rec (Map g ρ))

-- | Zip together two records that are the same up to the type being mapped over them,
-- combining their constituent fields with the given function.
zipTransform :: forall c r f g h .
  Forall r c => (forall a. c a => f a -> g a -> h a) -> Rec (Map f r) -> Rec (Map g r) -> Rec (Map h r)
zipTransform f x y = unRMap $ metamorph @_ @r @c @(,) @(RecMapPair f g) @(RMap h) @h Proxy doNil doUncons doCons $ RecMapPair x y
  where
    doNil _ = RMap empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
             => Label ℓ -> RecMapPair f g ρ -> (RecMapPair f g (ρ .- ℓ), h τ)
    doUncons l (RecMapPair x y) = (RecMapPair (lazyRemove l x) (lazyRemove l y), f (x .! l) (y .! l))
      \\ mapHas @f @ℓ @τ @ρ
      \\ mapHas @g @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> (RMap h ρ, h τ) -> RMap h (Extend ℓ τ ρ)
    doCons l (RMap r, h) = RMap (extend l h r)
      \\ mapExtendSwap @h @ℓ @τ @ρ

-- | A version of 'zipTransform' for when there is no constraint.
zipTransform' :: forall r f g h .
  FreeForall r => (forall a. f a -> g a -> h a) -> Rec (Map f r) -> Rec (Map g r) -> Rec (Map h r)
zipTransform' f = zipTransform @Unconstrained1 @r f

-- | Traverse a function over a record.  Note that the fields of the record will
-- be accessed in lexicographic order by the labels.
traverse :: forall c f r. (Forall r c, Applicative f) => (forall a. c a => a -> f a) -> Rec r -> f (Rec r)
traverse f = sequence' @f @r @c . map @c @f @r f

-- | Traverse a function over a Mapped record.  Note that the fields of the record will
-- be accessed in lexicographic order by the labels.
traverseMap :: forall c f g h r.
  (Forall r c, Applicative f) => (forall a. c a => g a -> f (h a)) -> Rec (Map g r) -> f (Rec (Map h r))
traverseMap f =
  sequence' @f @(Map h r) @(IsA c h) .
  uncompose' @c @f @h @r .
  transform @c @r @g @(Compose f h) (Compose . f)
  \\ mapForall @h @r @c

-- | A version of 'sequence' in which the constraint for 'Forall' can be chosen.
sequence' :: forall f r c. (Forall r c, Applicative f)
          => Rec (Map f r) -> f (Rec r)
sequence' = getCompose . metamorph @_ @r @c @(,) @(RMap f) @(Compose f Rec) @f Proxy doNil doUncons doCons . RMap
  where
    doNil _ = Compose (pure empty)
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
             => Label ℓ -> RMap f ρ -> (RMap f (ρ .- ℓ), f τ)
    doUncons l (RMap r) = first RMap $ lazyUncons l r
      \\ mapHas @f @ℓ @τ @ρ
    doCons l (Compose fr, fv) = Compose $ extend l <$> fv <*> fr

-- | Applicative sequencing over a record.
sequence :: forall f r. (Applicative f, FreeForall r)
         => Rec (Map f r) -> f (Rec r)
sequence = sequence' @_ @_ @Unconstrained1

-- | This function acts as the inversion of `sequence`, allowing one to move a
-- functor level into a record.
distribute :: forall f r. (FreeForall r, Functor f) => f (Rec r) -> Rec (Map f r)
distribute  = unRMap . metamorph @_ @r @Unconstrained1 @(,) @(Compose f Rec) @(RMap f) @f Proxy doNil doUncons doCons . Compose
  where
    doNil _ = RMap empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, HasType ℓ τ ρ)
             => Label ℓ -> Compose f Rec ρ -> (Compose f Rec (ρ .- ℓ), f τ)
    doUncons l (Compose fr) = (Compose $ lazyRemove l <$> fr, (.! l) <$> fr)
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ)
           => Label ℓ -> (RMap f ρ, f τ) -> RMap f (Extend ℓ τ ρ)
    doCons l (RMap r, fv) = RMap (extend l fv r)
      \\ mapExtendSwap @f @ℓ @τ @ρ


-- $compose
-- We can easily convert between mapping two functors over the types of a row
-- and mapping the composition of the two functors.  The following two functions
-- perform this composition with the gaurantee that:
--
-- >>> compose . uncompose = id
--
-- >>> uncompose . compose = id

-- | A version of 'compose' in which the constraint for 'Forall' can be chosen.
compose' :: forall c f g r . Forall r c
        => Rec (Map f (Map g r)) -> Rec (Map (Compose f g) r)
compose' = unRMap . metamorph @_ @r @c @(,) @(RMap2 f g) @(RMap (Compose f g)) @(Compose f g) Proxy doNil doUncons doCons . RMap2
  where
    doNil _ = RMap empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
             => Label ℓ -> RMap2 f g ρ -> (RMap2 f g (ρ .- ℓ), Compose f g τ)
    doUncons l (RMap2 r) = bimap RMap2 Compose $ lazyUncons l r
      \\ mapHas @f @ℓ @(g τ) @(Map g ρ)
      \\ mapHas @g @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> (RMap (Compose f g) ρ, Compose f g τ) -> RMap (Compose f g) (Extend ℓ τ ρ)
    doCons l (RMap r, v) = RMap $ extend l v r
      \\ mapExtendSwap @(Compose f g) @ℓ @τ @ρ

-- | Convert from a record where two functors have been mapped over the types to
-- one where the composition of the two functors is mapped over the types.
compose :: forall f g r . FreeForall r
        => Rec (Map f (Map g r)) -> Rec (Map (Compose f g) r)
compose = compose' @Unconstrained1 @f @g @r

-- | A version of 'uncompose' in which the constraint for 'Forall' can be chosen.
uncompose' :: forall c f g r . Forall r c
           => Rec (Map (Compose f g) r) -> Rec (Map f (Map g r))
uncompose' = unRMap2 . metamorph @_ @r @c @(,) @(RMap (Compose f g)) @(RMap2 f g) @(Compose f g) Proxy doNil doUncons doCons . RMap
  where
    doNil _ = RMap2 empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
             => Label ℓ -> RMap (Compose f g) ρ -> (RMap (Compose f g) (ρ .- ℓ), Compose f g τ)
    doUncons l (RMap r) = first RMap $ lazyUncons l r
      \\ mapHas @(Compose f g) @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> (RMap2 f g ρ, Compose f g τ) -> RMap2 f g (Extend ℓ τ ρ)
    doCons l (RMap2 r, Compose v) = RMap2 $ extend l v r
      \\ mapExtendSwap @f @ℓ @(g τ) @(Map g ρ)
      \\ mapExtendSwap @g @ℓ @τ @ρ

-- | Convert from a record where the composition of two functors have been mapped
-- over the types to one where the two functors are mapped individually one at a
-- time over the types.
uncompose :: forall f g r . FreeForall r
          => Rec (Map (Compose f g) r) -> Rec (Map f (Map g r))
uncompose = uncompose' @Unconstrained1 @f @g @r


-- | Coerce a record to a coercible representation.  The 'BiForall' in the context
-- indicates that the type of every field in @r1@ can be coerced to the type of
-- the corresponding fields in @r2@.
--
-- Internally, this is implemented just with `unsafeCoerce`, but we provide the
-- following implementation as a proof:
--
-- > newtype ConstR a b = ConstR (Rec a)
-- > newtype FlipConstR a b = FlipConstR { unFlipConstR :: Rec b }
-- > coerceRec :: forall r1 r2. BiForall r1 r2 Coercible => Rec r1 -> Rec r2
-- > coerceRec = unFlipConstR . biMetamorph @_ @_ @r1 @r2 @Coercible @(,) @ConstR @FlipConstR @Const Proxy doNil doUncons doCons . ConstR
-- >   where
-- >     doNil _ = FlipConstR empty
-- >     doUncons l (ConstR r) = bimap ConstR Const $ lazyUncons l r
-- >     doCons :: forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, Coercible τ1 τ2)
-- >            => Label ℓ -> (FlipConstR ρ1 ρ2, Const τ1 τ2) -> FlipConstR (Extend ℓ τ1 ρ1) (Extend ℓ τ2 ρ2)
-- >     doCons l (FlipConstR r, Const v) = FlipConstR $ extend l (coerce @τ1 @τ2 v) r
coerceRec :: forall r1 r2. BiForall r1 r2 Coercible => Rec r1 -> Rec r2
coerceRec = unsafeCoerce


-- | RZipPair is used internally as a type level lambda for zipping records.
newtype RecPair  (ρ1 :: Row *) (ρ2 :: Row *) = RecPair  (Rec ρ1, Rec ρ2)
newtype RZipPair (ρ1 :: Row *) (ρ2 :: Row *) = RZipPair { unRZipPair :: Rec (Zip ρ1 ρ2) }

-- | Zips together two records that have the same set of labels.
zip :: forall r1 r2. FreeBiForall r1 r2 => Rec r1 -> Rec r2 -> Rec (Zip r1 r2)
zip r1 r2 = unRZipPair $ biMetamorph @_ @_ @r1 @r2 @Unconstrained2 @(,) @RecPair @RZipPair @(,) Proxy doNil doUncons doCons $ RecPair (r1, r2)
  where
    doNil _ = RZipPair empty
    doUncons l (RecPair (r1, r2)) = (RecPair (lazyRemove l r1, lazyRemove l r2), (r1 .! l, r2 .! l))
    doCons :: forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ)
           => Label ℓ -> (RZipPair ρ1 ρ2, (τ1, τ2)) -> RZipPair (Extend ℓ τ1 ρ1) (Extend ℓ τ2 ρ2)
    doCons l (RZipPair r, vs) = RZipPair $ extend l vs r
      \\ zipExtendSwap @ℓ @τ1 @ρ1 @τ2 @ρ2

{--------------------------------------------------------------------
  Record initialization
--------------------------------------------------------------------}

-- | Initialize a record with a default value at each label.
default' :: forall c ρ. (Forall ρ c, AllUniqueLabels ρ) => (forall a. c a => a) -> Rec ρ
default' v = runIdentity $ defaultA @c $ pure v

-- | Initialize a record with a default value at each label; works over an 'Applicative'.
defaultA :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
         => (forall a. c a => f a) -> f (Rec ρ)
defaultA v = fromLabelsA @c $ pure v

-- | Initialize a record, where each value is determined by the given function over
-- the label at that value.
fromLabels :: forall c ρ. (Forall ρ c, AllUniqueLabels ρ)
           => (forall l a. (KnownSymbol l, c a) => Label l -> a) -> Rec ρ
fromLabels f = runIdentity $ fromLabelsA @c $ (pure .) f

-- | Initialize a record, where each value is determined by the given function over
-- the label at that value.  This function works over an 'Applicative'.
fromLabelsA :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
            => (forall l a. (KnownSymbol l, c a) => Label l -> f a) -> f (Rec ρ)
fromLabelsA mk = getCompose $ metamorph @_ @ρ @c @Const @(Const ()) @(Compose f Rec) @Proxy Proxy doNil doUncons doCons (Const ())
  where doNil _ = Compose $ pure empty
        doUncons _ _ = Const $ Const ()
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => Label ℓ -> Const (Compose f Rec ρ) (Proxy τ) -> Compose f Rec (Extend ℓ τ ρ)
        doCons l (Const (Compose r)) = Compose $ extend l <$> mk @ℓ @τ l <*> r

-- | Initialize a record over a `Map`.
fromLabelsMapA :: forall c f g ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
               => (forall l a. (KnownSymbol l, c a) => Label l -> f (g a)) -> f (Rec (Map g ρ))
fromLabelsMapA f = fromLabelsA @(IsA c g) @f @(Map g ρ) inner
                \\ mapForall @g @ρ @c
                \\ uniqueMap @g @ρ
   where inner :: forall l a. (KnownSymbol l, IsA c g a) => Label l -> f a
         inner l = case as @c @g @a of As -> f l


{--------------------------------------------------------------------
  Dynamic compatibility
--------------------------------------------------------------------}

-- | Converts a 'Rec' into a 'HashMap' of 'Dynamic's.
toDynamicMap :: Forall r Typeable => Rec r -> HashMap Text Dynamic
toDynamicMap = eraseToHashMap @Typeable @_ @Text @Dynamic toDyn

-- | Produces a 'Rec' from a 'HashMap' of 'Dynamic's.
fromDynamicMap :: (AllUniqueLabels r, Forall r Typeable)
               => HashMap Text Dynamic -> Maybe (Rec r)
fromDynamicMap m = fromLabelsA @Typeable
  $ \ (toKey -> k) -> M.lookup k m >>= fromDynamic


{--------------------------------------------------------------------
  Generic instance
--------------------------------------------------------------------}

-- The generic structure we want Recs to have is not the hidden internal one,
-- but rather one that appears as a Haskell record.  Thus, we can't derive
-- Generic automatically.
--
-- The following Generic instance creates a representation of a Rec that is
-- very similar to a native Haskell record except that the tree of pairs (':*:')
-- that it produces will be extremely unbalanced.  I don't think this is a problem.
-- Furthermore, because we don't want Recs to always have a trailing unit on
-- the end, we must have a special case for singleton Recs, which means that
-- we can't use metamorph.

instance GenericRec r => G.Generic (Rec r) where
  type Rep (Rec r) =
    G.D1 ('G.MetaData "Rec" "Data.Row.Records" "row-types" 'False)
      (G.C1 ('G.MetaCons "Rec" 'G.PrefixI 'True)
        (RepRec r))
  from = G.M1 . G.M1 . fromRec
  to = toRec . G.unM1 . G.unM1

class GenericRec r where
  type RepRec (r :: Row *) :: * -> *
  fromRec :: Rec r -> RepRec r x
  toRec   :: RepRec r x -> Rec r

instance GenericRec Empty where
  type RepRec (R '[]) = G.U1
  fromRec _ = G.U1
  toRec _ = empty

instance KnownSymbol name => GenericRec (R '[name :-> t]) where
  type RepRec (R (name :-> t ': '[])) = G.S1
    ('G.MetaSel ('Just name) 'G.NoSourceUnpackedness 'G.NoSourceStrictness 'G.DecidedLazy)
    (G.Rec0 t)
  fromRec (_ :== a) = G.M1 (G.K1 a)
  toRec (G.M1 (G.K1 a)) = (Label @name) :== a

instance
    ( r ~ (name' :-> t' ': r'), GenericRec (R r)
    , KnownSymbol name, Extend name t ('R r) ≈ 'R (name :-> t ': r)
    ) => GenericRec (R (name :-> t ': (name' :-> t' ': r'))) where
  type RepRec (R (name :-> t ': (name' :-> t' ': r'))) = (G.S1
    ('G.MetaSel ('Just name) 'G.NoSourceUnpackedness 'G.NoSourceStrictness 'G.DecidedLazy)
    (G.Rec0 t)) G.:*: RepRec (R (name' :-> t' ': r'))
  fromRec r = G.M1 (G.K1 (r .! Label @name)) G.:*: fromRec (lazyRemove @name Label r)
  toRec (G.M1 (G.K1 a) G.:*: r) = extend @_ @name @('R (name' :-> t' ': r')) Label a (toRec r)

{--------------------------------------------------------------------
  Native data type compatibility
--------------------------------------------------------------------}
-- ToNative is shamelessly copied from
--   https://www.athiemann.net/2017/07/02/superrecord.html

-- $native
-- The 'toNative' and 'fromNative' functions allow one to convert between
-- 'Rec's and regular Haskell data types ("native" types) that have a single constructor and any
-- number of named fields with the same names and types as the 'Rec'.  As expected,
-- they compose to form the identity.  Alternatively, one may use 'toNativeGeneral',
-- which allows fields to be dropped when a record has excess fields compared
-- to the native type.  Because of this, 'toNativeGeneral' requires a type
-- application (although 'fromNative' does not).  The only requirement is that
-- the native Haskell data type be an instance of 'Generic'.
--
-- For example, consider the following simple data type:
--
-- >>> data Person = Person { name :: String, age :: Int} deriving (Generic, Show)
--
-- Then, we have the following:
--
-- >>> toNative @Person $ #name .== "Alice" .+ #age .== 7 .+ #hasDog .== True
-- Person {name = "Alice", age = 7}
-- >>> fromNative $ Person "Bob" 9
-- { age=9, name="Bob" }

type family NativeRow t where
  NativeRow t = NativeRowG (G.Rep t)

type family NativeRowG t where
  NativeRowG (G.M1 G.D m cs) = NativeRowG cs
  NativeRowG (G.M1 G.C m cs) = NativeRowG cs
  NativeRowG G.U1 = Empty
  NativeRowG (l G.:*: r) = NativeRowG l .+ NativeRowG r
  NativeRowG (G.M1 G.S ('G.MetaSel ('Just name) p s l) (G.Rec0 t)) = name .== t


-- | Conversion helper to turn a Haskell record into a row-types extensible
-- record. Note that the native Haskell type must be an instance of 'Generic'.
class FromNativeG a where
  fromNative' :: a x -> Rec (NativeRowG a)

instance FromNativeG cs => FromNativeG (G.D1 m cs) where
  fromNative' (G.M1 xs) = fromNative' xs

instance FromNativeG cs => FromNativeG (G.C1 m cs) where
  fromNative' (G.M1 xs) = fromNative' xs

instance FromNativeG G.U1 where
  fromNative' G.U1 = empty

instance KnownSymbol name => FromNativeG (G.S1 ('G.MetaSel ('Just name) p s l) (G.Rec0 t)) where
  fromNative' (G.M1 (G.K1 x)) =  (Label @name) .== x

instance (FromNativeG l, FromNativeG r, FreeForall (NativeRowG l)) => FromNativeG (l G.:*: r) where
  fromNative' (x G.:*: y) = fromNative' @l x .+ fromNative' @r y

type FromNative t = (G.Generic t, FromNativeG (G.Rep t))

-- | Convert a Haskell record to a row-types Rec.
fromNative :: FromNative t => t -> Rec (NativeRow t)
fromNative = fromNative' . G.from


-- | Conversion helper to bring a record back into a Haskell type. Note that the
-- native Haskell type must be an instance of 'Generic'.
class ToNativeG a where
  toNative' :: Rec (NativeRowG a) -> a x

instance ToNativeG cs => ToNativeG (G.D1 m cs) where
  toNative' xs = G.M1 $ toNative' xs

instance ToNativeG cs => ToNativeG (G.C1 m cs) where
  toNative' xs = G.M1 $ toNative' xs

instance ToNativeG G.U1 where
  toNative' _ = G.U1

instance (KnownSymbol name) => ToNativeG (G.S1 ('G.MetaSel ('Just name) p s l) (G.Rec0 t)) where
  toNative' r = G.M1 $ G.K1 $ r .! (Label @name)

instance (ToNativeG l, ToNativeG r, Disjoint (NativeRowG l) (NativeRowG r))
    => ToNativeG (l G.:*: r) where
  toNative' r = toNative' r1 G.:*: toNative' r2
    where
      (r1 :: Rec (NativeRowG l)) :+ (r2 :: Rec (NativeRowG r)) = r

type ToNative t = (G.Generic t, ToNativeG (G.Rep t))

-- | Convert a record to an exactly matching native Haskell type.
toNative :: ToNative t => Rec (NativeRow t) -> t
toNative = G.to . toNative'



-- | Conversion helper to bring a record back into a Haskell type. Note that the
-- native Haskell type must be an instance of 'Generic'.
class ToNativeGeneralG a ρ where
  toNativeGeneral' :: Rec ρ -> a x

instance ToNativeGeneralG cs ρ => ToNativeGeneralG (G.D1 m cs) ρ where
  toNativeGeneral' xs = G.M1 $ toNativeGeneral' xs

instance ToNativeGeneralG cs ρ => ToNativeGeneralG (G.C1 m cs) ρ where
  toNativeGeneral' xs = G.M1 $ toNativeGeneral' xs

instance ToNativeGeneralG G.U1 ρ where
  toNativeGeneral' _ = G.U1

instance (KnownSymbol name, ρ .! name ≈ t)
    => ToNativeGeneralG (G.S1 ('G.MetaSel ('Just name) p s l) (G.Rec0 t)) ρ where
  toNativeGeneral' r = G.M1 $ G.K1 $ r .! (Label @name)

instance (ToNativeGeneralG l ρ, ToNativeGeneralG r ρ)
    => ToNativeGeneralG (l G.:*: r) ρ where
  toNativeGeneral' r = toNativeGeneral' r G.:*: toNativeGeneral' r

type ToNativeGeneral t ρ = (G.Generic t, ToNativeGeneralG (G.Rep t) ρ)

-- | Convert a record to a native Haskell type.
toNativeGeneral :: ToNativeGeneral t ρ => Rec ρ -> t
toNativeGeneral = G.to . toNativeGeneral'


{--------------------------------------------------------------------
  Generic-lens compatibility
--------------------------------------------------------------------}

-- | Every field in a row-types based record has a 'HasField' instance.
instance {-# OVERLAPPING #-}
  ( KnownSymbol name
  , r' .! name ≈ b
  , r  .! name ≈ a
  , r' ~ Modify name b r
  , r  ~ Modify name a r')
  => HasField name (Rec r) (Rec r') a b where
  field = focus (Label @name)
  {-# INLINE field #-}

instance {-# OVERLAPPING #-}
  ( KnownSymbol name
  , r .! name ≈ a
  , r ~ Modify name a r)
  => HasField' name (Rec r) a where
  field' = focus (Label @name)
  {-# INLINE field' #-}
