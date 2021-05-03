{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Row.Internal
--
-- This module implements the internals of open records and variants.
--
-----------------------------------------------------------------------------


module Data.Row.Internal
  (
  -- * Rows
    Row(..)
  , Label(..)
  , KnownSymbol
  , LT(..)
  , Empty
  , HideType(..)
  -- * Row Operations
  , Extend, Modify, Rename
  , type (.==), type (.!), type (.-), type (.\\)
  -- $merges
  , type (.+), type (.\/), type (.//)
  -- * Row Constraints
  , Lacks, type (.\), HasType
  , Forall(..)
  , BiForall(..)
  , BiConstraint
  , Unconstrained
  , Unconstrained1
  , Unconstrained2
  , FrontExtends(..)
  , FrontExtendsDict(..)
  , WellBehaved, AllUniqueLabels
  , Ap, ApSingle, Zip, Map, Subset, Disjoint
  -- * Helper functions
  , Labels, labels, labels'
  , show'
  , toKey
  , type (≈)
  )
where

import Data.Bifunctor (Bifunctor(..))
import Data.Constraint
import Data.Functor.Const
import Data.Proxy
import Data.String (IsString (fromString))
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Type.Equality (type (==))

import GHC.OverloadedLabels
import GHC.TypeLits
import qualified GHC.TypeLits as TL




{--------------------------------------------------------------------
  Rows
--------------------------------------------------------------------}
-- | The kind of rows. This type is only used as a datakind. A row is a typelevel entity telling us
--   which symbols are associated with which types.
newtype Row a = R [LT a]
  -- ^ A row is a list of symbol-to-type pairs that should always be sorted
  -- lexically by the symbol.
  -- The constructor is exported here (because this is an internal module) but
  -- should not be exported elsewhere.

-- | The kind of elements of rows.  Each element is a label and its associated type.
data LT a = Symbol :-> a


-- | A label
data Label (s :: Symbol) = Label
  deriving (Eq)

instance KnownSymbol s => Show (Label s) where
  show = symbolVal

instance x ≈ y => IsLabel x (Label y) where
#if __GLASGOW_HASKELL__ >= 802
  fromLabel = Label
#else
  fromLabel _ = Label
#endif

-- | A helper function for showing labels
show' :: (IsString s, Show a) => a -> s
show' = fromString . show

-- | A helper function to turn a Label directly into 'Text'.
toKey :: forall s. KnownSymbol s => Label s -> Text
toKey = Text.pack . symbolVal

-- | Type level version of 'empty'
type Empty = R '[]

-- | Elements stored in a Row type are usually hidden.
data HideType where
  HideType :: a -> HideType



{--------------------------------------------------------------------
  Row operations
--------------------------------------------------------------------}

infixl 4 .\ {- This comment needed to appease CPP -}
-- | Does the row lack (i.e. it does not have) the specified label?
type family (r :: Row k) .\ (l :: Symbol) :: Constraint where
  R '[] .\ l = Unconstrained
  R r   .\ l = LacksR l r r

-- | Type level Row extension
type family Extend (l :: Symbol) (a :: k) (r :: Row k) :: Row k where
  Extend l a (R '[]) = R (l :-> a ': '[])
  Extend l a (R x)   = R (Inject (l :-> a) x)

-- | Type level Row modification
type family Modify (l :: Symbol) (a :: k) (r :: Row k) :: Row k where
  Modify l a (R ρ) = R (ModifyR l a ρ)

-- | Type level row renaming
type family Rename (l :: Symbol) (l' :: Symbol) (r :: Row k) :: Row k where
  Rename l l' r = Extend  l' (r .! l) (r .- l)

infixl 5 .!
-- | Type level label fetching
type family (r :: Row k) .! (t :: Symbol) :: k where
  R r .! l = Get l r

infixl 6 .-
-- | Type level Row element removal
type family (r :: Row k) .- (s :: Symbol) :: Row k where
  R r .- l = R (Remove l r)

infixl 6 .\\ {- This comment needed to appease CPP -}
-- | Type level Row difference.  That is, @l '.\\' r@ is the row remaining after
-- removing any matching elements of @r@ from @l@.
type family (l :: Row k) .\\ (r :: Row k) :: Row k where
  R l .\\ R r = R (Diff l r)

-- $merges
-- == Various row-type merges
-- The difference between '.+' (read "append"), '.\/' (read "min-join"), and
-- '.\\' (read "const-union") comes down to how duplicates are handled.
-- In '.+', the two given row-types must be entirely unique.  Even the same
-- entry in both row-types is forbidden.  In '.\/', this final restriction is
-- relaxed, allowing two row-types that have no conflicts to be merged in the
-- logical way.  The '.\\' operator is the most liberal, allowing any two row-types
-- to be merged together, and whenever there is a conflict, favoring the left argument.
--
-- As examples of use:
--
-- - '.+' is used when appending two records, assuring that those two records are
--   entirely disjoint.
--
-- - '.\/' is used when diversifying a variant, allowing some extension to the
--   row-type so long as no original types have changed.
--
-- - './/' is used when doing record overwrite, allowing data in a record to
-- totally overwrite what was previously there.

infixl 6 .+
-- | Type level Row append
type family (l :: Row k) .+ (r :: Row k) :: Row k where
  x .+ R '[] = x
  R '[] .+ y = y
  x .+ R '[l :-> a] = Extend l a x
  R '[l :-> a] .+ y = Extend l a y
  R l .+ R r = R (Merge l r)

infixl 6 .\/
-- | The minimum join of the two rows.
type family (l :: Row k) .\/ (r :: Row k) where
  x .\/ R '[] = x
  R '[] .\/ y = y
  R l .\/ R r = R (MinJoinR l r)

infixl 6 .//
-- | The overwriting union, where the left row overwrites the types of the right
-- row where the labels overlap.
type family (l :: Row k) .// (r :: Row k) where
  x .// R '[] = x
  R '[] .// y = y
  R l .// R r = R (ConstUnionR l r)


{--------------------------------------------------------------------
  Syntactic sugar for record operations
--------------------------------------------------------------------}
-- | Alias for '.\'. It is a class rather than an alias, so that
-- it can be partially applied.
class Lacks (l :: Symbol) (r :: Row *)
instance (r .\ l) => Lacks l r


-- | Alias for @(r .! l) ≈ a@. It is a class rather than an alias, so that
-- it can be partially applied.
class (r .! l ≈ a) => HasType l a r
instance (r .! l ≈ a) => HasType l a r

-- | A type level way to create a singleton Row.
infix 7 .==
type (l :: Symbol) .== (a :: k) = Extend l a Empty


{--------------------------------------------------------------------
  Constrained record operations
--------------------------------------------------------------------}

-- | A dictionary of information that proves that extending a row-type @r@ with
-- a label @l@ will necessarily put it to the front of the underlying row-type
-- list.  This is quite internal and should not generally be necessary.
data FrontExtendsDict l t r = forall ρ. FrontExtendsDict (Dict (r ~ R ρ, R (l :-> t ': ρ) ≈ Extend l t (R ρ), AllUniqueLabelsR (l :-> t ': ρ)))

-- | A class wrapper for 'FrontExtendsDict'.
class FrontExtends l t r where
  frontExtendsDict :: FrontExtendsDict l t r

instance (r ~ R ρ, R (l :-> t ': ρ) ≈ Extend l t (R ρ), AllUniqueLabelsR (l :-> t ': ρ)) => FrontExtends l t r where
  frontExtendsDict = FrontExtendsDict Dict


-- | Any structure over a row in which every element is similarly constrained can
-- be metamorphized into another structure over the same row.
class Forall (r :: Row k) (c :: k -> Constraint) where
  -- | A metamorphism is an anamorphism (an unfold) followed by a catamorphism (a fold).
  -- The parameter 'p' describes the output of the unfold and the input of the fold.
  -- For records, @p = (,)@, because every entry in the row will unfold to a value paired
  -- with the rest of the record.
  -- For variants, @p = Either@, because there will either be a value or future types to
  -- explore.
  -- 'Const' can be useful when the types in the row are unnecessary.
  metamorph :: forall (p :: * -> * -> *) (f :: Row k -> *) (g :: Row k -> *) (h :: k -> *). Bifunctor p
            => Proxy (Proxy h, Proxy p)
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
               => Label ℓ -> f ρ -> p (f (ρ .- ℓ)) (h τ))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ, FrontExtends ℓ τ ρ, AllUniqueLabels (Extend ℓ τ ρ))
               => Label ℓ -> p (g ρ) (h τ) -> g (Extend ℓ τ ρ))
               -- ^ The fold
            -> f r  -- ^ The input structure
            -> g r

instance Forall (R '[]) c where
  {-# INLINE metamorph #-}
  metamorph _ empty _ _ = empty

instance (KnownSymbol ℓ, c τ, Forall ('R ρ) c, FrontExtends ℓ τ ('R ρ), AllUniqueLabels (Extend ℓ τ ('R ρ))) => Forall ('R (ℓ :-> τ ': ρ) :: Row k) c where
  {-# INLINE metamorph #-}
  metamorph h empty uncons cons = case frontExtendsDict @ℓ @τ @('R ρ) of
    FrontExtendsDict Dict ->
      cons (Label @ℓ) . first (metamorph @_ @('R ρ) @c h empty uncons cons) . uncons (Label @ℓ)


-- | Any structure over two rows in which the elements of each row satisfy some
--   constraints can be metamorphized into another structure over both of the
--   rows.
class BiForall (r1 :: Row k1) (r2 :: Row k2) (c :: k1 -> k2 -> Constraint) where
  -- | A metamorphism is an anamorphism (an unfold) followed by a catamorphism (a fold).
  biMetamorph :: forall (p :: * -> * -> *) (f :: Row k1 -> Row k2 -> *) (g :: Row k1 -> Row k2 -> *)
                        (h :: k1 -> k2 -> *). Bifunctor p
              => Proxy (Proxy h, Proxy p)
              -> (f Empty Empty -> g Empty Empty)
              -> (forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, c τ1 τ2, HasType ℓ τ1 ρ1, HasType ℓ τ2 ρ2)
                  => Label ℓ -> f ρ1 ρ2 -> p (f (ρ1 .- ℓ) (ρ2 .- ℓ)) (h τ1 τ2))
              -> (forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, c τ1 τ2, FrontExtends ℓ τ1 ρ1, FrontExtends ℓ τ2 ρ2, AllUniqueLabels (Extend ℓ τ1 ρ1), AllUniqueLabels (Extend ℓ τ2 ρ2))
                  => Label ℓ -> p (g ρ1 ρ2) (h τ1 τ2) -> g (Extend ℓ τ1 ρ1) (Extend ℓ τ2 ρ2))
              -> f r1 r2 -> g r1 r2


instance BiForall (R '[]) (R '[]) c1 where
  {-# INLINE biMetamorph #-}
  biMetamorph _ empty _ _ = empty

instance (KnownSymbol ℓ, c τ1 τ2, BiForall ('R ρ1) ('R ρ2) c, FrontExtends ℓ τ1 ('R ρ1), FrontExtends ℓ τ2 ('R ρ2), AllUniqueLabels (Extend ℓ τ1 ('R ρ1)), AllUniqueLabels (Extend ℓ τ2 ('R ρ2)))
      => BiForall ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2)) c where
  {-# INLINE biMetamorph #-}
  biMetamorph h empty uncons cons = case (frontExtendsDict @ℓ @τ1 @('R ρ1), frontExtendsDict @ℓ @τ2 @('R ρ2)) of
    (FrontExtendsDict Dict, FrontExtendsDict Dict) ->
      cons (Label @ℓ) . first (biMetamorph @_ @_ @('R ρ1) @('R ρ2) @c h empty uncons cons) . uncons (Label @ℓ)


-- | A null constraint
class Unconstrained
instance Unconstrained

-- | A null constraint of one argument
class Unconstrained1 a
instance Unconstrained1 a

-- | A null constraint of two arguments
class Unconstrained2 a b
instance Unconstrained2 a b

-- | A pair of constraints
class (c1 x, c2 y) => BiConstraint c1 c2 x y
instance (c1 x, c2 y) => BiConstraint c1 c2 x y

-- | The labels in a Row.
type family Labels (r :: Row a) where
  Labels (R '[]) = '[]
  Labels (R (l :-> a ': xs)) = l ': Labels (R xs)

-- | Return a list of the labels in a row type.
labels :: forall ρ c s. (IsString s, Forall ρ c) => [s]
labels = getConst $ metamorph @_ @ρ @c @Const @(Const ()) @(Const [s]) @Proxy Proxy (const $ Const []) doUncons doCons (Const ())
  where doUncons _ _ = Const $ Const ()
        doCons l (Const (Const c)) = Const $ show' l : c

-- | Return a list of the labels in a row type and is specialized to the 'Unconstrained1' constraint.
labels' :: forall ρ s. (IsString s, Forall ρ Unconstrained1) => [s]
labels' = labels @ρ @Unconstrained1


{--------------------------------------------------------------------
  Convenient type families and classes
--------------------------------------------------------------------}

-- | A convenient way to provide common, easy constraints
type WellBehaved ρ = (Forall ρ Unconstrained1, AllUniqueLabels ρ)

-- | Are all of the labels in this Row unique?
type family AllUniqueLabels (r :: Row k) :: Constraint where
  AllUniqueLabels (R r) = AllUniqueLabelsR r

type family AllUniqueLabelsR (r :: [LT k]) :: Constraint where
  AllUniqueLabelsR '[] = Unconstrained
  AllUniqueLabelsR '[l :-> a] = Unconstrained
  AllUniqueLabelsR (l :-> a ': l :-> b ': _) = TypeError
    (TL.Text "The label " :<>: ShowType l :<>: TL.Text " is not unique."
    :$$: TL.Text "It is assigned to both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b)
  AllUniqueLabelsR (l :-> a ': l' :-> b ': r) = AllUniqueLabelsR (l' :-> b ': r)

-- | Is the first row a subset of the second?
-- Or, does the second row contain every binding that the first one does?
type family Subset (r1 :: Row k) (r2 :: Row k) :: Constraint where
  Subset ('R '[]) r = Unconstrained
  Subset ('R (l ':-> a ': x)) r = (r .! l ≈ a, Subset ('R x) r)

-- | A type synonym for disjointness.
type Disjoint l r = ( WellBehaved l
                    , WellBehaved r
                    , Subset l (l .+ r)
                    , Subset r (l .+ r)
                    , l .+ r .\\ l ≈ r
                    , l .+ r .\\ r ≈ l)

-- | Map a type level function over a Row.
type family Map (f :: a -> b) (r :: Row a) :: Row b where
  Map f (R r) = R (MapR f r)

type family MapR (f :: a -> b) (r :: [LT a]) :: [LT b] where
  MapR f '[] = '[]
  MapR f (l :-> v ': t) = l :-> f v ': MapR f t

-- | Take two rows with the same labels, and apply the type operator from the
-- first row to the type of the second.
type family Ap (fs :: Row (a -> b)) (r :: Row a) :: Row b where
  Ap (R fs) (R r) = R (ApR fs r)

type family ApR (fs :: [LT (a -> b)]) (r :: [LT a]) :: [LT b] where
  ApR '[] '[] = '[]
  ApR (l :-> f ': tf) (l :-> v ': tv) = l :-> f v ': ApR tf tv
  ApR _ _ = TypeError (TL.Text "Row types with different label sets cannot be App'd together.")

-- | Take a row of type operators and apply each to the second argument.
type family ApSingle (fs :: Row (a -> b)) (x :: a) :: Row b where
  ApSingle (R fs) x = R (ApSingleR fs x)

type family ApSingleR (fs :: [LT (a -> b)]) (x :: a) :: [LT b] where
  ApSingleR '[] _ = '[]
  ApSingleR (l ':-> f ': fs) x = l ':-> f x ': ApSingleR fs x

-- | Zips two rows together to create a Row of the pairs.
--   The two rows must have the same set of labels.
type family Zip (r1 :: Row *) (r2 :: Row *) where
  Zip (R r1) (R r2) = R (ZipR r1 r2)

type family ZipR (r1 :: [LT *]) (r2 :: [LT *]) where
  ZipR '[] '[] = '[]
  ZipR (l :-> t1 ': r1) (l :-> t2 ': r2) =
    l :-> (t1, t2) ': ZipR r1 r2
  ZipR (l :-> t1 ': r1) _ = TypeError (TL.Text "Row types with different label sets cannot be zipped"
                                  :$$: TL.Text "For one, the label " :<>: ShowType l :<>: TL.Text " is not in both lists.")
  ZipR '[] (l :-> t ': r) = TypeError (TL.Text "Row types with different label sets cannot be zipped"
                                  :$$: TL.Text "For one, the label " :<>: ShowType l :<>: TL.Text " is not in both lists.")

type family Inject (l :: LT k) (r :: [LT k]) where
  Inject (l :-> t) '[] = (l :-> t ': '[])
  Inject (l :-> t) (l :-> t' ': x) = TypeError (TL.Text "Cannot inject a label into a row type that already has that label"
                                  :$$: TL.Text "The label " :<>: ShowType l :<>: TL.Text " was already assigned the type "
                                  :<>: ShowType t' :<>: TL.Text " and is now trying to be assigned the type "
                                  :<>: ShowType t :<>: TL.Text ".")
  Inject (l :-> t) (l' :-> t' ': x) =
      Ifte (l <=.? l')
      (l :-> t   ': l' :-> t' ': x)
      (l' :-> t' ': Inject (l :-> t)  x)

-- | Type level Row modification helper
type family ModifyR (l :: Symbol) (a :: k) (ρ :: [LT k]) :: [LT k] where
  ModifyR l a (l :-> a' ': ρ) = l :-> a ': ρ
  ModifyR l a (l' :-> a' ': ρ) = l' :-> a' ': ModifyR l a ρ
  ModifyR l a '[] = TypeError (TL.Text "Tried to modify the label " :<>: ShowType l
                          :<>: TL.Text ", but it does not appear in the row-type.")

type family Ifte (c :: Bool) (t :: k) (f :: k)   where
  Ifte True  t f = t
  Ifte False t f = f

type family Get (l :: Symbol) (r :: [LT k]) where
  Get l '[] = TypeError (TL.Text "No such field: " :<>: ShowType l)
  Get l (l :-> t ': x) = t
  Get l (l' :-> t ': x) = Get l x

type family Remove (l :: Symbol) (r :: [LT k]) where
  Remove l r = RemoveT l r r

type family RemoveT (l :: Symbol) (r :: [LT k]) (r_orig :: [LT k]) where
  RemoveT l (l :-> t ': x) _ = x
  RemoveT l (l' :-> t ': x) r = l' :-> t ': RemoveT l x r
  RemoveT l '[] r = TypeError (TL.Text "Cannot remove a label that does not occur in the row type."
                          :$$: TL.Text "The label " :<>: ShowType l :<>: TL.Text " is not in "
                          :<>: ShowRowType r)

type family LacksR (l :: Symbol) (r :: [LT k]) (r_orig :: [LT k]) :: Constraint where
  LacksR l '[] _ = Unconstrained
  LacksR l (l :-> t ': x) r = TypeError (TL.Text "The label " :<>: ShowType l
                                    :<>: TL.Text " already exists in " :<>: ShowRowType r)
  LacksR l (l' :-> _ ': x) r = Ifte (l <=.? l') Unconstrained (LacksR l x r)


type family Merge (l :: [LT k]) (r :: [LT k]) where
  Merge '[] r = r
  Merge l '[] = l
  Merge (h :-> a ': tl)   (h :-> a ': tr) =
    TypeError (TL.Text "The label " :<>: ShowType h :<>: TL.Text " (of type "
          :$$: ShowType a :<>: TL.Text ") has duplicate assignments.")
  Merge (h :-> a ': tl)   (h :-> b ': tr) =
    TypeError (TL.Text "The label " :<>: ShowType h :<>: TL.Text " has conflicting assignments."
          :$$: TL.Text "Its type is both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b :<>: TL.Text ".")
  Merge (hl :-> al ': tl) (hr :-> ar ': tr) =
      -- Using Ifte here makes GHC blow up on nested unions with many overlapping keys.
      MergeCont (CmpSymbol hl hr) hl al tl hr ar tr

type family MergeCont (cmp :: Ordering) (hl :: Symbol) (al :: k) (tl :: [LT k])
                                        (hr :: Symbol) (ar :: k) (tr :: [LT k]) where
    MergeCont 'LT hl al tl hr ar tr = (hl :-> al ': Merge tl (hr :-> ar ': tr))
    MergeCont _ hl al tl hr ar tr = (hr :-> ar ': Merge (hl :-> al ': tl) tr)

type family MinJoinR (l :: [LT k]) (r :: [LT k]) where
  MinJoinR '[] r = r
  MinJoinR l '[] = l
  MinJoinR (h :-> a ': tl)   (h :-> a ': tr) =
      (h :-> a ': MinJoinR tl tr)
  MinJoinR (h :-> a ': tl)   (h :-> b ': tr) =
    TypeError (TL.Text "The label " :<>: ShowType h :<>: TL.Text " has conflicting assignments."
          :$$: TL.Text "Its type is both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b :<>: TL.Text ".")
  MinJoinR (hl :-> al ': tl) (hr :-> ar ': tr) =
      -- Using Ifte here makes GHC blow up on nested unions with many overlapping keys.
      MinJoinRCase (CmpSymbol hl hr) hl al tl hr ar tr

type family MinJoinRCase (cmp :: Ordering) (hl :: Symbol) (al :: k) (tl :: [LT k])
                                           (hr :: Symbol) (ar :: k) (tr :: [LT k]) where
  MinJoinRCase 'LT hl al tl hr ar tr = hl :-> al ': MinJoinR tl (hr :-> ar ': tr)
  MinJoinRCase _   hl al tl hr ar tr = hr :-> ar ': MinJoinR (hl :-> al ': tl) tr

type family ConstUnionR (l :: [LT k]) (r :: [LT k]) where
  ConstUnionR '[] r = r
  ConstUnionR l '[] = l
  ConstUnionR (h :-> a ': tl)   (h :-> b ': tr) =
      (h :-> a ': ConstUnionR tl tr)
  ConstUnionR (hl :-> al ': tl) (hr :-> ar ': tr) =
      -- Using Ifte here makes GHC blow up on nested unions with many overlapping keys.
      ConstUnionRCase (CmpSymbol hl hr) hl al tl hr ar tr

type family ConstUnionRCase (cmp :: Ordering) (hl :: Symbol) (al :: k) (tl :: [LT k])
                                           (hr :: Symbol) (ar :: k) (tr :: [LT k]) where
  ConstUnionRCase 'LT hl al tl hr ar tr = hl :-> al ': ConstUnionR tl (hr :-> ar ': tr)
  ConstUnionRCase _   hl al tl hr ar tr = hr :-> ar ': ConstUnionR (hl :-> al ': tl) tr


-- | Returns the left list with all of the elements from the right list removed.
type family Diff (l :: [LT k]) (r :: [LT k]) where
  Diff '[] r = '[]
  Diff l '[] = l
  Diff (l ':-> al ': tl) (l ':-> al ': tr) = Diff tl tr
  Diff (hl ':-> al ': tl) (hr ':-> ar ': tr) =
    -- Using Ifte here makes GHC blow up on nested unions with many overlapping keys.
    DiffCont (CmpSymbol hl hr) hl al tl hr ar tr

type family DiffCont (cmp :: Ordering) (hl :: Symbol) (al :: k) (tl :: [LT k])
                                       (hr :: Symbol) (ar :: k) (tr :: [LT k]) where
    DiffCont 'LT hl al tl hr ar tr = (hl ':-> al ': Diff tl (hr ':-> ar ': tr))
    DiffCont _ hl al tl hr ar tr = (Diff (hl ':-> al ': tl) tr)

type family ShowRowType (r :: [LT k]) :: ErrorMessage where
  ShowRowType '[] = TL.Text "Empty"
  ShowRowType '[l ':-> t] = TL.ShowType l TL.:<>: TL.Text " .== " TL.:<>: TL.ShowType t
  ShowRowType ((l ':-> t) ': r) = TL.ShowType l TL.:<>: TL.Text " .== " TL.:<>: TL.ShowType t TL.:<>: TL.Text " .+ " TL.:<>: ShowRowType r

-- | There doesn't seem to be a (<=.?) :: Symbol -> Symbol -> Bool,
-- so here it is in terms of other ghc-7.8 type functions
type a <=.? b = (CmpSymbol a b == 'LT)

-- | A lower fixity operator for type equality
infix 4 ≈
type a ≈ b = a ~ b
