{-# LANGUAGE CPP #-}
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
  , type (.\), type (.!), type (.-), type (.+), type (.\\), type (.==)
  , type (.\/)
  , Lacks, HasType
  -- * Row Classes
  , Labels, labels, labels'
  , Forall(..)
  , BiForall(..)
  , BiConstraint
  , Unconstrained1
  , Unconstrained2
  -- * Helper functions
  , show'
  , toKey
  , type (≈)
  , WellBehaved, AllUniqueLabels, Ap, Zip, Map, Subset, Disjoint

  , mapForall
  , freeForall
  , uniqueMap
  , mapHas
  , IsA(..)
  , As(..)
  )
where

import Data.Constraint
import Data.Functor.Const
import Data.Proxy
import Data.String (IsString (fromString))
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Type.Equality (type (==))

import qualified Unsafe.Coerce as UNSAFE

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
  R r .\ l = LacksR l r r

-- | Type level Row extension
type family Extend (l :: Symbol) (a :: k) (r :: Row k) :: Row k where
  Extend l a (R x) = R (Inject (l :-> a) x)

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

infixl 6 .+
-- | Type level Row append
type family (l :: Row k) .+ (r :: Row k) :: Row k where
  R l .+ R r = R (Merge l r)

infixl 6 .\\ {- This comment needed to appease CPP -}
-- | Type level Row difference.  That is, @l .\\\\ r@ is the row remaining after
-- removing any matching elements of @r@ from @l@.
type family (l :: Row k) .\\ (r :: Row k) :: Row k where
  R l .\\ R r = R (Diff l r)

infixl 6 .\/
-- | The minimum join of the two rows.
type family (l :: Row k) .\/ (r :: Row k) where
  R l .\/ R r = R (MinJoinR l r)


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

-- | Any structure over a row in which every element is similarly constrained can
--   be metamorphized into another structure over the same row.
class Forall (r :: Row k) (c :: k -> Constraint) where
  -- | A metamorphism is an unfold followed by a fold.  This one is for
  -- product-like row-types (e.g. Rec).
  metamorph :: forall (f :: Row k -> *) (g :: Row k -> *) (h :: k -> *).
               Proxy h
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> f ('R (ℓ :-> τ ': ρ)) -> (h τ, f ('R ρ)))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> h τ -> g ('R ρ) -> g ('R (ℓ :-> τ ': ρ)))
               -- ^ The fold
            -> f r  -- ^ The input structure
            -> g r

  -- | A metamorphism is an unfold followed by a fold.  This one is for
  -- sum-like row-types (e.g. Var).
  metamorph' :: forall (f :: Row k -> *) (g :: Row k -> *) (h :: k -> *).
               Proxy h
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> f ('R (ℓ :-> τ ': ρ)) -> Either (h τ) (f ('R ρ)))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> Either (h τ) (g ('R ρ)) -> g ('R (ℓ :-> τ ': ρ)))
               -- ^ The fold
            -> f r  -- ^ The input structure
            -> g r

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
mapForall = Sub $ unMapForall $ metamorph @_ @ρ @c @(Const ()) @(MapForall c f) @(Const ()) Proxy empty uncons cons $ Const ()
  where empty :: Const () Empty -> MapForall c f Empty
        empty _ = MapForall Dict

        uncons :: forall l t r. (KnownSymbol l, c t)
               => Label l -> Const () ('R (l :-> t ': r)) -> (Const () t, Const () ('R r))
        uncons _ _ = (Const (), Const ())

        cons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
             => Label ℓ -> Const () τ -> MapForall c f ('R ρ)
             -> MapForall c f ('R (ℓ :-> τ ': ρ))
        cons _ _ (MapForall Dict) = MapForall Dict

-- | Map preserves uniqueness of labels.
uniqueMap :: forall f ρ. AllUniqueLabels ρ :- AllUniqueLabels (Map f ρ)
uniqueMap = Sub $ UNSAFE.unsafeCoerce @(Dict Unconstrained) Dict

-- | Allow any 'Forall` over a row-type, be usable for 'Unconstrained1'.
freeForall :: forall r c. Forall r c :- Forall r Unconstrained1
freeForall = Sub $ UNSAFE.unsafeCoerce @(Dict (Forall r c)) Dict

-- | This allows us to derive `Map f r .! l ≈ f t` from `r .! l ≈ t`
mapHas :: forall f r l t. (r .! l ≈ t) :- (Map f r .! l ≈ f t)
mapHas = Sub $ UNSAFE.unsafeCoerce $ Dict @(r .! l ≈ t)

instance Forall (R '[]) c where
  {-# INLINE metamorph #-}
  metamorph _ empty _ _ = empty
  {-# INLINE metamorph' #-}
  metamorph' _ empty _ _ = empty

instance (KnownSymbol ℓ, c τ, Forall ('R ρ) c) => Forall ('R (ℓ :-> τ ': ρ) :: Row k) c where
  metamorph :: forall (f :: Row k -> *) (g :: Row k -> *) (h :: k -> *).
               Proxy h
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> f ('R (ℓ :-> τ ': ρ)) -> (h τ, f ('R ρ)))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> h τ -> g ('R ρ) -> g ('R (ℓ :-> τ ': ρ)))
               -- ^ The fold
            -> f ('R (ℓ :-> τ ': ρ))  -- ^ The input structure
            -> g ('R (ℓ :-> τ ': ρ))
  {-# INLINE metamorph #-}
  metamorph _ empty uncons cons r = cons Label t $ metamorph @_ @('R ρ) @c @_ @_ @h Proxy empty uncons cons r'
    where (t, r') = uncons Label r
  metamorph' :: forall (f :: Row k -> *) (g :: Row k -> *) (h :: k -> *).
               Proxy h
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> f ('R (ℓ :-> τ ': ρ)) -> Either (h τ) (f ('R ρ)))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> Either (h τ) (g ('R ρ)) -> g ('R (ℓ :-> τ ': ρ)))
               -- ^ The fold
            -> f ('R (ℓ :-> τ ': ρ))  -- ^ The input structure
            -> g ('R (ℓ :-> τ ': ρ))
  {-# INLINE metamorph' #-}
  metamorph' _ empty uncons cons r = cons Label $ metamorph' @_ @('R ρ) @c @_ @_ @h Proxy empty uncons cons <$> uncons Label r

-- | Any structure over two rows in which the elements of each row satisfy some
--   constraints can be metamorphized into another structure over both of the
--   rows.
class BiForall (r1 :: Row k1) (r2 :: Row k2) (c :: k1 -> k2 -> Constraint) where
  -- | A metamorphism is a fold followed by an unfold.  This one is for
  -- product-like row-types.
  biMetamorph :: forall (f :: Row k1 -> Row k2 -> *) (g :: Row k1 -> Row k2 -> *)
                        (h :: k1 -> k2 -> *).
                 Proxy h
              -> (f Empty Empty -> g Empty Empty)
              -> (forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, c τ1 τ2)
                  => Label ℓ
                  -> f ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2))
                  -> (h τ1 τ2, f ('R ρ1) ('R ρ2)))
              -> (forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, c τ1 τ2)
                  => Label ℓ -> h τ1 τ2 -> g ('R ρ1) ('R ρ2) -> g ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2)))
              -> f r1 r2 -> g r1 r2

  -- | A metamorphism is a fold followed by an unfold.  This one is for
  -- sum-like row-types.
  biMetamorph' :: forall (f :: Row k1 -> Row k2 -> *) (g :: Row k1 -> Row k2 -> *)
                         (h :: k1 -> k2 -> *).
                  Proxy h
               -> (f Empty Empty -> g Empty Empty)
               -> (forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, c τ1 τ2)
                   => Label ℓ
                   -> f ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2))
                   -> Either (h τ1 τ2) (f ('R ρ1) ('R ρ2)))
               -> (forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, c τ1 τ2)
                   => Label ℓ -> Either (h τ1 τ2) (g ('R ρ1) ('R ρ2)) -> g ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2)))
               -> f r1 r2 -> g r1 r2

instance BiForall (R '[]) (R '[]) c1 where
  {-# INLINE biMetamorph #-}
  biMetamorph _ empty _ _ = empty
  biMetamorph' _ empty _ _ = empty

instance (KnownSymbol ℓ, c τ1 τ2, BiForall ('R ρ1) ('R ρ2) c)
      => BiForall ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2)) c where
  {-# INLINE biMetamorph #-}
  biMetamorph h empty uncons cons r = cons (Label @ℓ) t $ biMetamorph @_ @_ @('R ρ1) @('R ρ2) @c h empty uncons cons r'
    where (t, r') = uncons (Label @ℓ) r
  {-# INLINE biMetamorph' #-}
  biMetamorph' h empty uncons cons r =
    cons (Label @ℓ) $ biMetamorph' @_ @_ @('R ρ1) @('R ρ2) @c h empty uncons cons <$> uncons (Label @ℓ) r

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
labels = getConst $ metamorph @_ @ρ @c @(Const ()) @(Const [s]) @(Const ()) Proxy (const $ Const []) doUncons doCons (Const ())
  where doUncons _ _ = (Const (), Const ())
        doCons l _ (Const c) = Const $ show' l : c

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
type family Subset (r1 :: Row k) (r2 :: Row k) :: Constraint where
  Subset (R r1) (R r2) = SubsetR r1 r2

type family SubsetR (r1 :: [LT k]) (r2 :: [LT k]) :: Constraint where
  SubsetR '[] _ = Unconstrained
  SubsetR x '[] = TypeError (TL.Text "One row-type is not a subset of the other."
        :$$: TL.Text "The first contains the bindings " :<>: ShowType x
        :<>: TL.Text " while the second does not.")
  SubsetR (l :-> a ': x) (l :-> a ': y) = SubsetR x y
  SubsetR (l :-> a ': x) (l :-> b ': y) =
    TypeError (TL.Text "One row-type is not a subset of the other."
          :$$: TL.Text "The first assigns the label " :<>: ShowType l :<>: TL.Text " to "
          :<>: ShowType a :<>: TL.Text " while the second assigns it to " :<>: ShowType b)
  SubsetR (hl :-> al ': tl) (hr :-> ar ': tr) =
      Ifte (hl <=.? hr)
      (TypeError (TL.Text "One row-type is not a subset of the other."
             :$$: TL.Text "The first assigns the label " :<>: ShowType hl :<>: TL.Text " to "
             :<>: ShowType al :<>: TL.Text " while the second has no assignment for it."))
      (SubsetR (hl :-> al ': tl) tr)

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
type family Ap (fs :: Row (* -> *)) (r :: Row *) :: Row * where
  Ap (R fs) (R r) = R (ApR fs r)

type family ApR (fs :: [LT (* -> *)]) (r :: [LT *]) :: [LT *] where
  ApR '[] '[] = '[]
  ApR (l :-> f ': tf) (l :-> v ': tv) = l :-> f v ': ApR tf tv
  ApR _ _ = TypeError (TL.Text "Row types with different label sets cannot be App'd together.")

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
                          :<>: ShowType r)

type family LacksR (l :: Symbol) (r :: [LT k]) (r_orig :: [LT k]) :: Constraint where
  LacksR l '[] _ = Unconstrained
  LacksR l (l :-> t ': x) r = TypeError (TL.Text "The label " :<>: ShowType l
                                    :<>: TL.Text " already exists in " :<>: ShowType r)
  LacksR l (l' :-> _ ': x) r = Ifte (l <=.? l') Unconstrained (LacksR l x r)

type family Merge (l :: [LT k]) (r :: [LT k]) where
  Merge '[] r = r
  Merge l '[] = l
  Merge (h :-> a ': tl)   (h :-> b ': tr) =
    TypeError (TL.Text "The label " :<>: ShowType h :<>: TL.Text " has conflicting assignments."
          :$$: TL.Text "Its type is both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b :<>: TL.Text ".")
  Merge (hl :-> al ': tl) (hr :-> ar ': tr) =
      Ifte (hl <=.? hr)
      (hl :-> al ': Merge tl (hr :-> ar ': tr))
      (hr :-> ar ': Merge (hl :-> al ': tl) tr)

type family MinJoinR (l :: [LT k]) (r :: [LT k]) where
  MinJoinR '[] r = r
  MinJoinR l '[] = l
  MinJoinR (h :-> a ': tl)   (h :-> a ': tr) =
      (h :-> a ': MinJoinR tl tr)
  MinJoinR (h :-> a ': tl)   (h :-> b ': tr) =
    TypeError (TL.Text "The label " :<>: ShowType h :<>: TL.Text " has conflicting assignments."
          :$$: TL.Text "Its type is both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b :<>: TL.Text ".")
  MinJoinR (hl :-> al ': tl) (hr :-> ar ': tr) =
      Ifte (CmpSymbol hl hr == 'LT)
      (hl :-> al ': MinJoinR tl (hr :-> ar ': tr))
      (hr :-> ar ': MinJoinR (hl :-> al ': tl) tr)


-- | Returns the left list with all of the elements from the right list removed.
type family Diff (l :: [LT k]) (r :: [LT k]) where
  Diff '[] r = '[]
  Diff l '[] = l
  Diff (l :-> al ': tl) (l :-> al ': tr) = Diff tl tr
  Diff (hl :-> al ': tl) (hr :-> ar ': tr) =
    Ifte (hl <=.? hr)
    (hl :-> al ': Diff tl (hr :-> ar ': tr))
    (Diff (hl :-> al ': tl) tr)

-- | There doesn't seem to be a (<=.?) :: Symbol -> Symbol -> Bool,
-- so here it is in terms of other ghc-7.8 type functions
type a <=.? b = (CmpSymbol a b == 'LT)

-- | A lower fixity operator for type equality
infix 4 ≈
type a ≈ b = a ~ b
