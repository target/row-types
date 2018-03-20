{-# LANGUAGE CPP #-}
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
  , Lacks, HasType
  -- * Row Classes
  , Labels, labels, labels'
  , Forall(..), Forall2(..)
  , Unconstrained1
  -- * Helper functions
  , show'
  , toKey
  , type (≈)
  , WellBehaved, AllUniqueLabels, Zip, Map, Subset, Disjoint

  , mapForall
  , freeForall
  , uniqueMap
  , IsA(..)
  , As(..)

  , FoldStep
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
type family (r :: Row *) .\ (l :: Symbol) :: Constraint where
  R r .\ l = LacksR l r r

-- | Type level Row extension
type family Extend (l :: Symbol) (a :: *) (r :: Row *) :: Row * where
  Extend l a (R x) = R (Inject (l :-> a) x)

-- | Type level Row modification
type family Modify (l :: Symbol) (a :: *) (r :: Row *) :: Row * where
  Modify l a (R ρ) = R (ModifyR l a ρ)

-- | Type level row renaming
type family Rename (l :: Symbol) (l' :: Symbol) (r :: Row *) :: Row * where
  Rename l l' r = Extend  l' (r .! l) (r .- l)

infixl 5 .!
-- | Type level label fetching
type family (r :: Row *) .! (t :: Symbol) :: * where
  R r .! l = Get l r

infixl 6 .-
-- | Type level Row element removal
type family (r :: Row *) .- (s :: Symbol) :: Row * where
  R r .- l = R (Remove l r)

infixl 6 .+
-- | Type level Row append
type family (l :: Row *) .+ (r :: Row *) :: Row * where
  R l .+ R r = R (Merge l r)

infixl 6 .\\ {- This comment needed to appease CPP -}
-- | Type level Row difference.  That is, @l .\\\\ r@ is the row remaining after
-- removing any matching elements of @r@ from @l@.
type family (l :: Row *) .\\ (r :: Row *) :: Row * where
  R l .\\ R r = R (Diff l r)

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
type (l :: Symbol) .== (a :: *) = Extend l a Empty


{--------------------------------------------------------------------
  Constrained record operations
--------------------------------------------------------------------}

-- | Proof that the given label is a valid candidate for the next step
-- in a metamorph fold, i.e. it's not in the list yet and, when sorted,
-- will be placed at the head.
type FoldStep ℓ τ ρ = ( Inject (ℓ :-> τ) ρ ≈ ℓ :-> τ ': ρ
                      , R ρ .\ ℓ
                      )

-- | Any structure over a row in which every element is similarly constrained can
--   be metamorphized into another structure over the same row.
class Forall (r :: Row *) (c :: * -> Constraint) where
  -- | A metamorphism is an unfold followed by a fold.  This one is for
  -- product-like row-types (e.g. Rec).
  metamorph :: forall (f :: Row * -> *) (g :: Row * -> *) (h :: * -> *).
               Proxy h
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> f ('R (ℓ :-> τ ': ρ)) -> (h τ, f ('R ρ)))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ, FoldStep ℓ τ ρ) => Label ℓ -> h τ -> g ('R ρ) -> g ('R (ℓ :-> τ ': ρ)))
               -- ^ The fold
            -> f r  -- ^ The input structure
            -> g r

  -- | A metamorphism is an unfold followed by a fold.  This one is for
  -- sum-like row-types (e.g. Var).
  metamorph' :: forall (f :: Row * -> *) (g :: Row * -> *) (h :: * -> *).
               Proxy h
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> f ('R (ℓ :-> τ ': ρ)) -> Either (h τ) (f ('R ρ)))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ, FoldStep ℓ τ ρ) => Label ℓ -> Either (h τ) (g ('R ρ)) -> g ('R (ℓ :-> τ ': ρ)))
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
newtype MapForall c f (r :: Row *) = MapForall { unMapForall :: Dict (Forall (Map f r) (IsA c f)) }

-- | This allows us to derive a `Forall (Map f r) ..` from a `Forall r ..`.
mapForall :: forall f c ρ. Forall ρ c :- Forall (Map f ρ) (IsA c f)
mapForall = Sub $ unMapForall $ metamorph @ρ @c @(Const ()) @(MapForall c f) @(Const ()) Proxy empty uncons cons $ Const ()
  where empty :: Const () Empty -> MapForall c f Empty
        empty _ = MapForall Dict

        uncons :: forall l t r. (KnownSymbol l, c t)
               => Label l -> Const () ('R (l :-> t ': r)) -> (Const () t, Const () ('R r))
        uncons _ _ = (Const (), Const ())

        cons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ, FoldStep ℓ τ ρ)
             => Label ℓ -> Const () τ -> MapForall c f ('R ρ)
             -> MapForall c f ('R (ℓ :-> τ ': ρ))
        cons _ _ (MapForall Dict) =
           case UNSAFE.unsafeCoerce @(Dict Unconstrained) @(Dict (FoldStep ℓ (f τ) (MapR f ρ))) Dict of
             Dict -> MapForall Dict

-- | Map preserves uniqueness of labels.
uniqueMap :: forall f ρ. AllUniqueLabels ρ :- AllUniqueLabels (Map f ρ)
uniqueMap = Sub $ UNSAFE.unsafeCoerce @(Dict Unconstrained) Dict

-- | Allow any 'Forall` over a row-type, be usable for 'Unconstrained1'.
freeForall :: forall r c. Forall r c :- Forall r Unconstrained1
freeForall = Sub $ UNSAFE.unsafeCoerce @(Dict (Forall r c)) Dict

instance Forall (R '[]) c where
  {-# INLINE metamorph #-}
  metamorph _ empty _ _ = empty
  {-# INLINE metamorph' #-}
  metamorph' _ empty _ _ = empty

instance (KnownSymbol ℓ, c τ, FoldStep ℓ τ ρ, Forall ('R ρ) c) => Forall ('R (ℓ :-> τ ': ρ)) c where
  metamorph :: forall (f :: Row * -> *) (g :: Row * -> *) (h :: * -> *).
               Proxy h
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> f ('R (ℓ :-> τ ': ρ)) -> (h τ, f ('R ρ)))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ, FoldStep ℓ τ ρ) => Label ℓ -> h τ -> g ('R ρ) -> g ('R (ℓ :-> τ ': ρ)))
               -- ^ The fold
            -> f ('R (ℓ :-> τ ': ρ))  -- ^ The input structure
            -> g ('R (ℓ :-> τ ': ρ))
  {-# INLINE metamorph #-}
  metamorph _ empty uncons cons r = cons Label t $ metamorph @('R ρ) @c @_ @_ @h Proxy empty uncons cons r'
    where (t, r') = uncons Label r
  metamorph' :: forall (f :: Row * -> *) (g :: Row * -> *) (h :: * -> *).
               Proxy h
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Label ℓ -> f ('R (ℓ :-> τ ': ρ)) -> Either (h τ) (f ('R ρ)))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ, FoldStep ℓ τ ρ) => Label ℓ -> Either (h τ) (g ('R ρ)) -> g ('R (ℓ :-> τ ': ρ)))
               -- ^ The fold
            -> f ('R (ℓ :-> τ ': ρ))  -- ^ The input structure
            -> g ('R (ℓ :-> τ ': ρ))
  {-# INLINE metamorph' #-}
  metamorph' _ empty uncons cons r = cons Label $ metamorph' @('R ρ) @c @_ @_ @h Proxy empty uncons cons <$> uncons Label r

-- | Any structure over two rows in which every element of both rows satisfies the
--   given constraint can be metamorphized into another structure over both of the
--   rows.
-- TODO: Perhaps it should be over two constraints?  But this hasn't seemed necessary
--  in practice.
class Forall2 (r1 :: Row *) (r2 :: Row *) (c :: * -> Constraint) where
  -- | A metamorphism is a fold followed by an unfold.  Here, we fold both of the inputs.
  metamorph2 :: forall (f :: Row * -> *) (g :: Row * -> *) (h :: Row * -> Row * -> *)
                       (f' :: * -> *) (g' :: * -> *).
                Proxy f' -> Proxy g'
             -> (f Empty -> g Empty -> h Empty Empty)
             -> (forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, c τ1, c τ2)
                 => Label ℓ
                 -> f ('R (ℓ :-> τ1 ': ρ1))
                 -> g ('R (ℓ :-> τ2 ': ρ2))
                 -> ((f' τ1, f ('R ρ1)), (g' τ2, g ('R ρ2))))
             -> (forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, c τ1, c τ2)
                 => Label ℓ -> f' τ1 -> g' τ2 -> h ('R ρ1) ('R ρ2) -> h ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2)))
             -> f r1 -> g r2 -> h r1 r2

instance Forall2 (R '[]) (R '[]) c where
  {-# INLINE metamorph2 #-}
  metamorph2 _ _ empty _ _ = empty

instance (KnownSymbol ℓ, c τ1, c τ2, Forall2 ('R ρ1) ('R ρ2) c)
      => Forall2 ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2)) c where
  {-# INLINE metamorph2 #-}
  metamorph2 f g empty uncons cons r1 r2 = cons (Label @ℓ) t1 t2 $ metamorph2 @('R ρ1) @('R ρ2) @c f g empty uncons cons r1' r2'
    where ((t1, r1'), (t2, r2')) = uncons (Label @ℓ) r1 r2

-- | A null constraint
class Unconstrained
instance Unconstrained

-- | A null constraint of one argument
class Unconstrained1 a
instance Unconstrained1 a

-- | The labels in a Row.
type family Labels (r :: Row a) where
  Labels (R '[]) = '[]
  Labels (R (l :-> a ': xs)) = l ': Labels (R xs)

-- | Return a list of the labels in a row type.
labels :: forall ρ c s. (IsString s, Forall ρ c) => [s]
labels = getConst $ metamorph @ρ @c @(Const ()) @(Const [s]) @(Const ()) Proxy (const $ Const []) doUncons doCons (Const ())
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
type family AllUniqueLabels (r :: Row *) :: Constraint where
  AllUniqueLabels (R r) = AllUniqueLabelsR r

type family AllUniqueLabelsR (r :: [LT *]) :: Constraint where
  AllUniqueLabelsR '[] = Unconstrained
  AllUniqueLabelsR '[l :-> a] = Unconstrained
  AllUniqueLabelsR (l :-> a ': l :-> b ': _) = TypeError
    (TL.Text "The label " :<>: ShowType l :<>: TL.Text " is not unique."
    :$$: TL.Text "It is assigned to both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b)
  AllUniqueLabelsR (l :-> a ': l' :-> b ': r) = AllUniqueLabelsR (l' :-> b ': r)

-- | Is the first row a subset of the second?
type family Subset (r1 :: Row *) (r2 :: Row *) :: Constraint where
  Subset (R r1) (R r2) = SubsetR r1 r2

type family SubsetR (r1 :: [LT *]) (r2 :: [LT *]) :: Constraint where
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

type family Inject (l :: LT *) (r :: [LT *]) where
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
type family ModifyR (l :: Symbol) (a :: *) (ρ :: [LT *]) :: [LT *] where
  ModifyR l a (l :-> a' ': ρ) = l :-> a ': ρ
  ModifyR l a (l' :-> a' ': ρ) = l' :-> a' ': ModifyR l a ρ
  ModifyR l a '[] = TypeError (TL.Text "Tried to modify the label " :<>: ShowType l
                          :<>: TL.Text ", but it does not appear in the row-type.")

type family Ifte (c :: Bool) (t :: k) (f :: k)   where
  Ifte True  t f = t
  Ifte False t f = f

type family Get (l :: Symbol) (r :: [LT *]) where
  Get l '[] = TypeError (TL.Text "No such field: " :<>: ShowType l)
  Get l (l :-> t ': x) = t
  Get l (l' :-> t ': x) = Get l x

type family Remove (l :: Symbol) (r :: [LT *]) where
  Remove l r = RemoveT l r r

type family RemoveT (l :: Symbol) (r :: [LT *]) (r_orig :: [LT *]) where
  RemoveT l (l :-> t ': x) _ = x
  RemoveT l (l' :-> t ': x) r = l' :-> t ': RemoveT l x r
  RemoveT l '[] r = TypeError (TL.Text "Cannot remove a label that does not occur in the row type."
                          :$$: TL.Text "The label " :<>: ShowType l :<>: TL.Text " is not in "
                          :<>: ShowType r)

type family LacksR (l :: Symbol) (r :: [LT *]) (r_orig :: [LT *]) :: Constraint where
  LacksR l '[] r = Unconstrained
  LacksR l (l :-> t ': x) r = TypeError (TL.Text "The label " :<>: ShowType l
                                    :<>: TL.Text " already exists in " :<>: ShowType r)
  LacksR l (p ': x) r = LacksR l x r

type family Merge (l :: [LT *]) (r :: [LT *]) where
  Merge '[] r = r
  Merge l '[] = l
  Merge (h :-> a ': tl)   (h :-> a ': tr) =
      (h :-> a ': Merge tl tr)
  Merge (h :-> a ': tl)   (h :-> b ': tr) =
    TypeError (TL.Text "The label " :<>: ShowType h :<>: TL.Text " has conflicting assignments."
          :$$: TL.Text "Its type is both " :<>: ShowType a :<>: TL.Text " and " :<>: ShowType b :<>: TL.Text ".")
  Merge (hl :-> al ': tl) (hr :-> ar ': tr) =
      Ifte (hl <=.? hr)
      (hl :-> al ': Merge tl (hr :-> ar ': tr))
      (hr :-> ar ': Merge (hl :-> al ': tl) tr)

-- | Returns the left list with all of the elements from the right list removed.
type family Diff (l :: [LT *]) (r :: [LT *]) where
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
