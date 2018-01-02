-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Row.Records
--
-- This module implements extensible records using closed type famillies.
--
-- See Examples.hs for examples.
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
  , KnownSymbol, AllUniqueLabels
  , Rec, Row, Empty
  -- * Construction
  , empty
  , type (.==), (.==)
  , defaultRecord, defaultRecordA
  , recordFromLabels, recordFromLabelsA
  , rinit, rinitA, rinitAWithLabel
  -- ** Extension
  , Extendable(..), Extend, Lacks, type (.\)
  -- ** Restriction
  , type (.-), (.-)
  , restrict, recSplit
  -- ** Modification
  , Updatable(..), Focusable(..), Modify, Renamable(..), Rename
  -- * Query
  , HasType, type (.!), (.!)
  -- * Combine
  -- ** Disjoint union
  , type (.+), (.+)
  -- * Row operations
  -- ** Map
  , Map, rmap, rmapc, rxform, rxformc
  -- ** Fold
  , Forall, Erasable(..), eraseToHashMap, Unconstrained1
  -- ** Zip
  , RZip, rzip
  -- ** Sequence
  , rsequence
  -- ** Labels
  , labels
  )
where

import Control.DeepSeq (NFData(..), deepseq)

import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Hashable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as M
import Data.List
import Data.Proxy
import Data.String (IsString)
import Data.Text (Text)

import GHC.TypeLits

import Unsafe.Coerce

import Data.Row.Internal





{--------------------------------------------------------------------
  Open records
--------------------------------------------------------------------}
-- | A record with row r.
data Rec (r :: Row *) where
  OR :: HashMap Text HideType -> Rec r

instance Forall r Show => Show (Rec r) where
  show r = "{ " ++ intercalate ", " binds ++ " }"
    where binds = (\ (x, y) -> x ++ "=" ++ y) <$> eraseWithLabels (Proxy @Show) show r

instance Forall r Eq => Eq (Rec r) where
  r == r' = and $ eraseZip (Proxy @Eq) (==) r r'

instance (Eq (Rec r), Forall r Ord) => Ord (Rec r) where
  compare m m' = cmp $ eraseZip (Proxy @Ord) compare m m'
      where cmp l | [] <- l' = EQ
                  | a : _ <- l' = a
                  where l' = dropWhile (== EQ) l

instance (Forall r Bounded, AllUniqueLabels r) => Bounded (Rec r) where
  minBound = defaultRecord @Bounded minBound
  maxBound = defaultRecord @Bounded maxBound

instance Forall r NFData => NFData (Rec r) where
  rnf r = getConst $ metamorph @r @NFData @Rec @(Const ()) @Identity Proxy empty doUncons doCons r
    where empty = const $ Const ()
          doUncons l r = (Identity $ r .! l, removeUNSAFE l r)
          doCons _ x r = deepseq x $ deepseq r $ Const ()

-- | The empty record
empty :: Rec Empty
empty = OR M.empty

-- | The singleton record
infixr 7 .==
(.==) :: KnownSymbol l => Label l -> a -> Rec (l .== a)
l .== a = extend l a empty

{--------------------------------------------------------------------
  Basic record operations
--------------------------------------------------------------------}


instance Extendable Rec where
  type Inp Rec a = a
  -- | Record extension. The row may already contain the label,
  --   in which case the origin value can be obtained after restriction ('.-') with
  --   the label.
  extend (toKey -> l) a (OR m) = OR $ M.insert l (HideType a) m


instance Updatable Rec where
  -- | Update the value associated with the label.
  update (toKey -> l) a (OR m) = OR $ M.adjust f l m where f = const (HideType a)


instance Focusable Rec where
  type FRequires Rec = Functor
  -- | Focus on the value associated with the label.
  focus (toKey -> l) f (OR m) = case m M.! l of
    HideType x -> OR . flip (M.insert l) m . HideType <$> f (unsafeCoerce x)


instance Renamable Rec where
  -- | Rename a label.
  rename (toKey -> l) (toKey -> l') (OR m) = OR $ M.insert l' (m M.! l) $ M.delete l m

-- | Record selection
(.!) :: KnownSymbol l => Rec r -> Label l -> r .! l
OR m .! (toKey -> a) = case m M.! a of
  HideType x -> unsafeCoerce x

infix  8 .-
-- | Record restriction. Remove the label l from the record.
(.-) :: KnownSymbol l => Rec r -> Label l -> Rec (r .- l)
-- OR m .- _ = OR m
OR m .- (toKey -> a) = OR $ M.delete a m

-- | Record disjoint union (commutative)
infixr 6 .+
(.+) :: Rec l -> Rec r -> Rec (l .+ r)
OR l .+ OR r = OR $ M.unionWith (error "Impossible") l r

-- | Split a record into two sub-records.
recSplit :: forall s r. (Forall s Unconstrained1, Subset s r)
         => Rec r -> (Rec s, Rec (r .\\ s))
recSplit (OR m) = (OR $ M.intersection m labelMap, OR $ M.difference m labelMap)
  where labelMap = M.fromList $ zip (labels @s @Unconstrained1) (repeat ())

-- | Arbitrary record restriction.  Turn a record into a subset of itself.
restrict :: forall r r'. (Forall r Unconstrained1, Subset r r') => Rec r' -> Rec r
restrict = fst . recSplit

-- | Removes a label from the record but does not remove the underlying value.
--
-- This is faster than regular record removal ('.-') but should only be used when
-- either: the record will never be merged with another record again, or a new
-- value will soon be placed into the record at this label (as in, an 'update'
-- that is split over two commands).
--
-- If the resulting record is then merged (with '.+') with another record that
-- contains a value at that label, an "Impossible" error will occur.
removeUNSAFE :: KnownSymbol l => Label l -> Rec r -> Rec (r .- l)
removeUNSAFE _ (OR m) = OR m


{--------------------------------------------------------------------
  Folds and maps
--------------------------------------------------------------------}
-- An easier type synonym for a pair where both elements are the same type.
type IPair = Product Identity Identity

-- Construct an IPair.
iPair :: τ -> τ -> IPair τ
iPair = (. Identity) . Pair . Identity

-- Destruct an IPair.  Easily used with ViewPatterns.
unIPair :: IPair τ -> (τ, τ)
unIPair (Pair (Identity x) (Identity y)) = (x,y)

instance Erasable Rec where
  type Output Rec a = [a]
  type OutputZip Rec a = [a]
  erase p f = fmap (snd @String) . eraseWithLabels p f

  eraseWithLabels :: forall s ρ c b. (Forall ρ c, IsString s) => Proxy c -> (forall a. c a => a -> b) -> Rec ρ -> [(s,b)]
  eraseWithLabels _ f = getConst . metamorph @ρ @c @Rec @(Const [(s,b)]) @Identity Proxy doNil doUncons doCons
    where doNil _ = Const []
          doUncons l r = (Identity $ r .! l, removeUNSAFE l r)
          doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => Label ℓ -> Identity τ -> Const [(s,b)] ('R ρ) -> Const [(s,b)] ('R (ℓ :-> τ ': ρ))
          doCons l (Identity x) (Const c) = Const $ (show' l, f x) : c

  eraseZip :: forall ρ c b. Forall ρ c => Proxy c -> (forall a. c a => a -> a -> b) -> Rec ρ -> Rec ρ -> [b]
  eraseZip _ f x y = getConst $ metamorph @ρ @c @(Product Rec Rec) @(Const [b]) @IPair Proxy (const $ Const []) doUncons doCons (Pair x y)
    where doUncons l (Pair r1 r2) = (iPair a b, Pair r1' r2')
            where (a, r1') = (r1 .! l, removeUNSAFE l r1)
                  (b, r2') = (r2 .! l, removeUNSAFE l r2)
          doCons :: forall ℓ τ ρ. c τ
                 => Label ℓ -> IPair τ -> Const [b] ('R ρ) -> Const [b] ('R (ℓ :-> τ ': ρ))
          doCons _ (unIPair -> x) (Const c) = Const $ uncurry f x : c

-- | Turns a record into a 'HashMap' from values representing the labels to
--   the values of the record.
eraseToHashMap :: (IsString s, Eq s, Hashable s, Forall r c) =>
                  Proxy c -> (forall a . c a => a -> b) -> Rec r -> HashMap s b
eraseToHashMap p f r = M.fromList $ eraseWithLabels p f r

-- | RMap is used internally as a type level lambda for defining record maps.
newtype RMap (f :: * -> *) (ρ :: Row *) = RMap { unRMap :: Rec (Map f ρ) }

-- | A function to map over a record given a constraint.
rmapc :: forall c f r. Forall r c => (forall a. c a => a -> f a) -> Rec r -> Rec (Map f r)
rmapc f = unRMap . metamorph @r @c @Rec @(RMap f) @Identity Proxy doNil doUncons doCons
  where
    doNil _ = RMap empty
    doUncons l r = (Identity $ r .! l, removeUNSAFE l r)
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> Identity τ -> RMap f ('R ρ) -> RMap f ('R (ℓ :-> τ ': ρ))
    doCons l (Identity v) (RMap r) = RMap (unsafeInjectFront l (f v) r)

-- | A function to map over a record given no constraint.
rmap :: forall f r. Forall r Unconstrained1 => (forall a. a -> f a) -> Rec r -> Rec (Map f r)
rmap = rmapc @Unconstrained1

-- | A record transformer to convert a record of @f a@ values to a record of @g a@ values
-- where the mapping function can use a constraint.
rxformc :: forall r c f g. Forall r c => (forall a. c a => f a -> g a) -> Rec (Map f r) -> Rec (Map g r)
rxformc f = unRMap . metamorph @r @c @(RMap f) @(RMap g) @f Proxy doNil doUncons doCons . RMap
  where
    doNil _ = RMap empty
    doUncons l (RMap r) = (r .! l, RMap $ removeUNSAFE l r)
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> f τ -> RMap g ('R ρ) -> RMap g ('R (ℓ :-> τ ': ρ))
    doCons l v (RMap r) = RMap (unsafeInjectFront l (f v) r)

-- | A record transformer to convert a record of @f a@ values to a record of @g a@ values.
rxform :: forall r f g . Forall r Unconstrained1 => (forall a. f a -> g a) -> Rec (Map f r) -> Rec (Map g r)
rxform = rxformc @r @Unconstrained1

-- | Applicative sequencing over a record
rsequence :: forall f r. (Forall r Unconstrained1, Applicative f) => Rec (Map f r) -> f (Rec r)
rsequence = getCompose . metamorph @r @Unconstrained1 @(RMap f) @(Compose f Rec) @f Proxy doNil doUncons doCons . RMap
  where
    doNil _ = Compose (pure empty)
    doUncons l (RMap r) = (r .! l, RMap $ removeUNSAFE l r)
    doCons l fv (Compose fr) = Compose $ unsafeInjectFront l <$> fv <*> fr

-- | RZipPair is used internally as a type level lambda for zipping records.
newtype RZipPair (ρ1 :: Row *) (ρ2 :: Row *) = RZipPair { unRZipPair :: Rec (RZip ρ1 ρ2) }

-- | Zips together two records that have the same set of labels.
rzip :: forall r1 r2. Forall2 r1 r2 Unconstrained1 => Rec r1 -> Rec r2 -> Rec (RZip r1 r2)
rzip r1 r2 = unRZipPair $ metamorph2 @r1 @r2 @Unconstrained1 @Rec @Rec @RZipPair @Identity @Identity Proxy Proxy doNil doUncons doCons r1 r2
  where
    doNil _ _ = RZipPair empty
    doUncons l r1 r2 = ((Identity $ r1 .! l, removeUNSAFE l r1), (Identity $ r2 .! l, removeUNSAFE l r2))
    doCons l (Identity v1) (Identity v2) (RZipPair r) = RZipPair $ unsafeInjectFront l (v1, v2) r

-- | A helper function for unsafely adding an element to the front of a record
unsafeInjectFront :: KnownSymbol l => Label l -> a -> Rec (R r) -> Rec (R (l :-> a ': r))
unsafeInjectFront (toKey -> a) b (OR m) = OR $ M.insert a (HideType b) m


{--------------------------------------------------------------------
  Record initialization
--------------------------------------------------------------------}

-- | Initialize a record with a default value at each label.
defaultRecord :: forall c ρ. (Forall ρ c, AllUniqueLabels ρ) => (forall a. c a => a) -> Rec ρ
defaultRecord v = runIdentity $ defaultRecordA @c $ pure v

-- | Initialize a record with a default value at each label; works over an 'Applicative'.
defaultRecordA :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
       => (forall a. c a => f a) -> f (Rec ρ)
defaultRecordA v = recordFromLabelsA @c $ pure v

-- | Initialize a record, where each value is determined by the given function over
-- the label at that value.
recordFromLabels :: forall c ρ. (Forall ρ c, AllUniqueLabels ρ)
                 => (forall l a. (KnownSymbol l, c a) => Label l -> a) -> Rec ρ
recordFromLabels f = runIdentity $ recordFromLabelsA @c $ (pure .) f

-- | Initialize a record, where each value is determined by the given function over
-- the label at that value.  This function works over an 'Applicative'.
recordFromLabelsA :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
                  => (forall l a. (KnownSymbol l, c a) => Label l -> f a) -> f (Rec ρ)
recordFromLabelsA mk = getCompose $ metamorph @ρ @c @(Const ()) @(Compose f Rec) @(Const ()) Proxy doNil doUncons doCons (Const ())
  where doNil _ = Compose $ pure empty
        doUncons _ _ = (Const (), Const ())
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => Label ℓ -> Const () τ -> Compose f Rec ('R ρ) -> Compose f Rec ('R (ℓ :-> τ ': ρ))
        doCons l _ (Compose r) = Compose $ unsafeInjectFront l <$> mk l <*> r



{-# DEPRECATED rinitAWithLabel "Use recordFromLabels or recordFromLabelsA instead" #-}
{-# DEPRECATED rinit, rinitA "Use defaultRecord or defaultRecordA instead" #-}
-- | Initialize a record, where each value is determined by the given function over
-- the label at that value.  This function works over an 'Applicative'.
rinitAWithLabel :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
                => (forall l a. (KnownSymbol l, c a) => Label l -> f a) -> f (Rec ρ)
rinitAWithLabel mk = getCompose $ metamorph @ρ @c @(Const ()) @(Compose f Rec) @(Const ()) Proxy doNil doUncons doCons (Const ())
  where doNil _ = Compose $ pure empty
        doUncons _ _ = (Const (), Const ())
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => Label ℓ -> Const () τ -> Compose f Rec ('R ρ) -> Compose f Rec ('R (ℓ :-> τ ': ρ))
        doCons l _ (Compose r) = Compose $ unsafeInjectFront l <$> mk l <*> r

-- | Initialize a record with a default value at each label; works over an 'Applicative'.
rinitA :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
       => (forall a. c a => f a) -> f (Rec ρ)
rinitA f = rinitAWithLabel @c $ pure f

-- | Initialize a record with a default value at each label.
rinit :: forall c ρ. (Forall ρ c, AllUniqueLabels ρ) => (forall a. c a => a) -> Rec ρ
rinit f = runIdentity $ rinitA @c $ pure f


