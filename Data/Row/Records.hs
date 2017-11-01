-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Records
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
  , type (=:), (=:)
  , rinit, rinitA, rinitAWithLabel
  -- ** Extension
  , Extendable(..), Extend, type (\:)
  -- ** Restriction
  , type (-:), (-:)
  , restrict
  -- ** Modification
  , Updatable(..), Focusable(..), Modify, Renamable(..), Rename
  -- * Query
  , type (!:), (!:)
  -- * Combine
  -- ** Disjoint union
  , Disjoint, type (+:), (+:)
  -- * Row operations
  -- ** Map
  , Map, rmapc, rmap, rxformc, rxform
  -- ** Fold
  , Forall(..), Erasable(..), eraseToHashMap, Unconstrained1
  -- ** Zip
  , RZip, rzip
  -- ** Sequence
  , rsequence
  -- ** labels
  , labels
  )
where

import Control.Monad.Identity

import Data.Functor.Const
import Data.Hashable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as M
import Data.List
import Data.Proxy
import Data.String (IsString)

import GHC.TypeLits

import Unsafe.Coerce

import Data.Row.Internal





{--------------------------------------------------------------------
  Open records
--------------------------------------------------------------------}
-- | A record with row r.
data Rec (r :: Row *) where
  OR :: HashMap String HideType -> Rec r

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
  minBound = rinit @Bounded minBound
  maxBound = rinit @Bounded maxBound

type instance ValOf Rec τ = τ

-- | The empty record
empty :: Rec Empty
empty = OR M.empty

-- | The singleton record
infixr 7 =:
(=:) :: KnownSymbol l => Label l -> a -> Rec (l =: a)
l =: a = extend l a empty

{--------------------------------------------------------------------
  Basic record operations
--------------------------------------------------------------------}


instance Extendable Rec where
  type Inp Rec a = a
  -- | Record extension. The row may already contain the label,
  --   in which case the origin value can be obtained after restriction ('.-') with
  --   the label.
  extend (show -> l) a (OR m) = OR $ M.insert l (HideType a) m


instance Updatable Rec where
  -- | Update the value associated with the label.
  update (show -> l) a (OR m) = OR $ M.adjust f l m where f = const (HideType a)


instance Focusable Rec where
  -- | Focus on the value associated with the label.
  focus (show -> l) f (OR m) = case m M.! l of
    HideType x -> OR . flip (M.insert l) m . HideType <$> f (unsafeCoerce x)


instance Renamable Rec where
  -- | Rename a label.
  rename (show -> l) (show -> l') (OR m) = OR $ M.insert l' (m M.! l) $ M.delete l m

-- | Record selection
(!:) :: KnownSymbol l => Rec r -> Label l -> r !: l
OR m !: (show -> a) = case m M.! a of
  HideType x -> unsafeCoerce x

infix  8 -:
-- | Record restriction. Delete the label l from the record.
(-:) :: KnownSymbol l =>  Rec r -> Label l -> Rec (r -: l)
OR m -: (show -> a) = OR $ M.delete a m

-- | Record disjoint union (commutative)
infixr 6 +:
(+:) :: Disjoint l r => Rec l -> Rec r -> Rec (l +: r)
OR l +: OR r = OR $ M.unionWith (error "Impossible") l r

-- | Arbitrary record restriction.  Turn a record into a subset of itself.
restrict :: forall r r'. Subset r r' => Rec r' -> Rec r
restrict (OR m) = OR m

-- | Removes a label from the record, returning the value at that label along
-- with the updated record.
remove :: KnownSymbol l => Label l -> Rec r -> (r !: l, Rec (r -: l))
remove l r = (r !: l, r -: l)


{--------------------------------------------------------------------
  Folds and maps
--------------------------------------------------------------------}
instance Erasable Rec where
  type Output Rec a = [a]
  type OutputZip Rec a = [a]
  erase p f = fmap (snd @String) . eraseWithLabels p f

  eraseWithLabels :: forall s ρ c b. (Forall ρ c, IsString s) => Proxy c -> (forall a. c a => a -> b) -> Rec ρ -> [(s,b)]
  eraseWithLabels _ f = getConst . metamorph @ρ @c @Rec @(Const [(s,b)]) doNil doUncons doCons
    where doNil _ = Const []
          doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                   => Rec ('R (ℓ :-> τ ': ρ)) -> (τ, Rec ('R ρ))
          doUncons = remove (Label @ℓ)
          doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => τ -> Const [(s,b)] ('R ρ) -> Const [(s,b)] ('R (ℓ :-> τ ': ρ))
          doCons x (Const c) = Const $ (show' (Label @ℓ), f x) : c

  eraseZip :: forall ρ c b. Forall ρ c => Proxy c -> (forall a. c a => a -> a -> b) -> Rec ρ -> Rec ρ -> [b]
  eraseZip _ f x y = getConst $ metamorph @ρ @c @(RowPair Rec) @(Const [b]) (const $ Const []) doUncons doCons (RowPair (x,y))
    where doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                   => (RowPair Rec) ('R (ℓ :-> τ ': ρ)) -> ((τ,τ), (RowPair Rec) ('R ρ))
          doUncons (RowPair (r1, r2)) = ((r1 !: l, r2 !: l), RowPair (r1 -: l, r2 -: l)) where l = Label @ℓ
          doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => (τ,τ) -> Const [b] ('R ρ) -> Const [b] ('R (ℓ :-> τ ': ρ))
          doCons x (Const c) = Const $ uncurry f x : c

-- | Turns a record into a 'HashMap' from values representing the labels to
--   the values of the record.
eraseToHashMap :: (IsString s, Eq s, Hashable s, Forall r c) =>
                  Proxy c -> (forall a . c a => a -> b) -> Rec r -> HashMap s b
eraseToHashMap p f r = M.fromList $ eraseWithLabels p f r

-- | RMap is used internally as a type level lambda for defining record maps.
newtype RMap (f :: * -> *) (ρ :: Row *) = RMap { unRMap :: Rec (Map f ρ) }
type instance ValOf (RMap f) τ = f τ

-- | A function to map over a record given a constraint.
rmapc :: forall c f r. Forall r c => (forall a. c a => a -> f a) -> Rec r -> Rec (Map f r)
rmapc f = unRMap . metamorph @r @c @Rec @(RMap f) doNil doUncons doCons
  where
    doNil _ = RMap empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Rec ('R (ℓ :-> τ ': ρ)) -> (τ, Rec ('R ρ))
    doUncons = remove (Label @ℓ)
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => τ -> RMap f ('R ρ) -> RMap f ('R (ℓ :-> τ ': ρ))
    doCons v (RMap r) = RMap (unsafeInjectFront l (f v) r) where l = Label @ℓ

-- | A function to map over a record given no constraint.
rmap :: forall f r. Forall r Unconstrained1 => (forall a. a -> f a) -> Rec r -> Rec (Map f r)
rmap = rmapc @Unconstrained1

-- | A mapping function specifically to convert @f a@ values to @g a@ values.
rxformc :: forall r c f g. Forall r c => (forall a. c a => f a -> g a) -> Rec (Map f r) -> Rec (Map g r)
rxformc f = unRMap . metamorph @r @c @(RMap f) @(RMap g) doNil doUncons doCons . RMap
  where
    doNil _ = RMap empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => RMap f ('R (ℓ :-> τ ': ρ)) -> (f τ, RMap f ('R ρ))
    doUncons (RMap r) = (r !: l, RMap $ r -: l) where l = Label @ℓ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => f τ -> RMap g ('R ρ) -> RMap g ('R (ℓ :-> τ ': ρ))
    doCons v (RMap r) = RMap (unsafeInjectFront l (f v) r) where l = Label @ℓ

-- | A form of @rxformc@ that doesn't have a constraint on @a@
rxform :: forall r f g . Forall r Unconstrained1 => (forall a. f a -> g a) -> Rec (Map f r) -> Rec (Map g r)
rxform = rxformc @r @Unconstrained1

-- | Applicative sequencing over a record
rsequence :: forall f r. (Forall r Unconstrained1, Applicative f) => Rec (Map f r) -> f (Rec r)
rsequence = unFRow . metamorph @r @Unconstrained1 @(RMap f) @(FRow Rec f) doNil doUncons doCons . RMap
  where
    doNil _ = FRow (pure empty)
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ) => RMap f ('R (ℓ :-> τ ': ρ)) -> (f τ, RMap f ('R ρ))
    doUncons (RMap r) = (r !: l, RMap $ r -: l) where l = Label @ℓ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ)
           => f τ -> FRow Rec f ('R ρ) -> FRow Rec f ('R (ℓ :-> τ ': ρ))
    doCons fv (FRow fr) = FRow $ unsafeInjectFront l <$> fv <*> fr where l = Label @ℓ

-- | RZipPair is used internally as a type level lambda for zipping records.
newtype RZipPair (ρ1 :: Row *) (ρ2 :: Row *) = RZipPair { unRZipPair :: Rec (RZip ρ1 ρ2) }

-- | Zips together two records that have the same set of labels.
rzip :: forall r1 r2. Forall2 r1 r2 Unconstrained1 => Rec r1 -> Rec r2 -> Rec (RZip r1 r2)
rzip r1 r2 = unRZipPair $ metamorph2 @r1 @r2 @Unconstrained1 @Rec @Rec @RZipPair doNil doUncons doCons r1 r2
  where
    doNil _ _ = RZipPair empty
    doUncons :: forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ)
        => Rec ('R (ℓ :-> τ1 ': ρ1))
        -> Rec ('R (ℓ :-> τ2 ': ρ2))
        -> ((τ1, Rec ('R ρ1)), (τ2, Rec ('R ρ2)))
    doUncons r1 r2 = (remove l r1, remove l r2) where l = Label @ℓ
    doCons :: forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ)
        => τ1 -> τ2 -> RZipPair ('R ρ1) ('R ρ2) -> RZipPair ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2))
    doCons v1 v2 (RZipPair r) = RZipPair $ unsafeInjectFront l (v1, v2) r where l = Label @ℓ

-- | A helper function for unsafely adding an element to the front of a record
unsafeInjectFront :: KnownSymbol l => Label l -> a -> Rec (R r) -> Rec (R (l :-> a ': r))
unsafeInjectFront (show -> a) b (OR m) = OR $ M.insert a (HideType b) m


{--------------------------------------------------------------------
  Record initialization
--------------------------------------------------------------------}

-- | Initialize a record, where each value is determined by the given function over
-- the label at that value.  This function works over an 'Applicative'.
rinitAWithLabel :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
                => (forall l a. (KnownSymbol l, c a) => Label l -> f a) -> f (Rec ρ)
rinitAWithLabel mk = unFRow $ metamorph @ρ @c @(Const ()) @(FRow Rec f) doNil doUncons doCons (Const ())
  where doNil :: Const () Empty -> FRow Rec f Empty
        doNil _ = FRow $ pure empty
        doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => Const () ('R (ℓ :-> τ ': ρ)) -> ((), Const () ('R ρ))
        doUncons _ = ((), Const ())
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => () -> FRow Rec f ('R ρ) -> FRow Rec f ('R (ℓ :-> τ ': ρ))
        doCons _ (FRow r) = FRow $ unsafeInjectFront (Label @ℓ) <$> mk @ℓ @τ (Label @ℓ) <*> r

-- | Initialize a record with a default value at each label; works over an 'Applicative'.
rinitA :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
       => (forall a. c a => f a) -> f (Rec ρ)
rinitA f = rinitAWithLabel @c $ pure f

-- | Initialize a record with a default value at each label.
rinit :: forall c ρ. (Forall ρ c, AllUniqueLabels ρ) => (forall a. c a => a) -> Rec ρ
rinit f = runIdentity $ rinitA @c $ pure f


