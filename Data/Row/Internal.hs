{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Internal.Row
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
  , Disjoint, Extend, Modify, Rename
  , type (.\), type (.!), type (.-), type (.+), type (.\\), type (.==)
  , Lacks, HasType
  -- * Row Classes
  , Labels, labels
  , Forall(..), Forall2(..)
  , Unconstrained1
  -- * Common operations on types over rows
  , Extendable(..)
  , Updatable(..)
  , Focusable(..)
  , Renamable(..)
  , Erasable(..)
  -- * Helper functions
  , show'
  , LacksL, Unique(..), AllUniqueLabels, RZip, Map, Subset
  )
where

import Data.Functor.Const
import Data.Proxy
import Data.String (IsString (fromString))
import Data.Type.Equality (type (==))

import GHC.Exts -- needed for constraints kinds
import GHC.OverloadedLabels
import GHC.TypeLits




{--------------------------------------------------------------------
  Rows
--------------------------------------------------------------------}
-- | The kind of rows. This type is only used as a datakind. A row is a typelevel entity telling us
--   which symbols are associated with which types.  The constructor is exported
--   here (because this is an internal module) but should not be exported elsewhere.
newtype Row a = R [LT a]

-- | The kind of elements of rows.  Each element is a label and its associated type.
data LT a = Symbol :-> a


-- | A label
data Label (s :: Symbol) = Label

instance KnownSymbol s => Show (Label s) where
  show = symbolVal

instance x ~ y => IsLabel x (Label y) where
#if __GLASGOW_HASKELL__ >= 802
  fromLabel = Label
#else
  fromLabel _ = Label
#endif

instance ( FRequires t f, KnownSymbol l, Focusable t
         , a' ~ (r .! l -> f a), b' ~ (t r -> f (t (Modify l a r))))
      => IsLabel l (a' -> b') where
#if __GLASGOW_HASKELL__ >= 802
  fromLabel = focus @t (Label @l)
#else
  fromLabel _ = focus @t (Label @l)
#endif


-- | A helper function for showing labels
show' :: (IsString s, Show a) => a -> s
show' = fromString . show

-- | Type level variant of 'empty'
type family Empty :: Row * where
  Empty = R '[]

-- | Elements stored in a Row type are usually hidden.
data HideType where
  HideType :: a -> HideType



{--------------------------------------------------------------------
  Row operations
--------------------------------------------------------------------}

-- | Does the row lack (i.e. it does not have) the specified label?
type r .\ l = (LacksP l r ~ LabelUnique l)

-- | Type level Row extension
type family Extend (l :: Symbol) (a :: *) (r :: Row *) :: Row * where
  Extend l a (R x) = R (Inject (l :-> a) x)

-- | Type level Row modification
type family Modify (l :: Symbol) (a :: *) (r :: Row *) :: Row * where
  Modify l a (R ρ) = R (ModifyR l a ρ)

-- | Type level Row modification helper
type family ModifyR (l :: Symbol) (a :: *) (ρ :: [LT *]) :: [LT *] where
  ModifyR l a (l :-> a' ': ρ) = l :-> a ': ρ
  ModifyR l a (l' :-> a' ': ρ) = l' :-> a' ': ModifyR l a ρ

-- | Type level row renaming
type family Rename (l :: Symbol) (l' :: Symbol) (r :: Row *) :: Row * where
  Rename l l' r = Extend  l' (r .! l) (r .- l)

infixl 6 .!
-- | Type level label fetching
type family (r :: Row *) .! (t :: Symbol) :: * where
  R r .! l = Get l r

-- | Type level Row element removal
type family (r :: Row *) .- (s :: Symbol) :: Row * where
  R r .- l = R (Remove l r)

infixr 6 .+
-- | Type level Row append
type family (l :: Row *) .+ (r :: Row *) :: Row * where
  R l .+ R r = R (Merge l r)

-- | Type level Row difference.  That is, @l :// r@ is the row remaining after
-- removing any matching elements of @r@ from @l@.
type family (l :: Row *) .\\ (r :: Row *) :: Row * where
  R l .\\ R r = R (Diff l r)

{--------------------------------------------------------------------
  Syntactic sugar for record operations
--------------------------------------------------------------------}
-- | Alias for ':\'. It is a class rather than an alias, so that
-- it can be partially applied.
class (r .\ l) => Lacks (l :: Symbol) (r :: Row *)
instance (r .\ l) => Lacks l r


-- | Alias for @(r .! l) ~ a@. It is a class rather than an alias, so that
-- it can be partially applied.
class ((r .! l) ~ a) => HasType l a r
instance ((r .! l) ~ a) => HasType l a r

-- | A type level way to create a singleton Row.
infixr 7 .==
type (l :: Symbol) .== (a :: *) = Extend l a Empty


{--------------------------------------------------------------------
  Constrained record operations
--------------------------------------------------------------------}

-- | Proof that the given label is a valid candidate for the next step
-- in a metamorph fold, i.e. it's not in the list yet and, when sorted,
-- will be placed at the head.
type FoldStep ℓ τ ρ = ( (Inject (ℓ :-> τ) ρ) ~ (ℓ :-> τ ': ρ)
                      , LacksR ℓ ρ ~ LabelUnique ℓ
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

instance Forall (R '[]) c where
  metamorph _ empty _ _ = empty
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
  metamorph2 _ _ empty _ _ = empty

instance (KnownSymbol ℓ, c τ1, c τ2, Forall2 ('R ρ1) ('R ρ2) c)
      => Forall2 ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2)) c where
  metamorph2 f g empty uncons cons r1 r2 = cons (Label @ℓ) t1 t2 $ metamorph2 @('R ρ1) @('R ρ2) @c f g empty uncons cons r1' r2'
    where ((t1, r1'), (t2, r2')) = uncons (Label @ℓ) r1 r2

-- | A null constraint
class Unconstrained1 a
instance Unconstrained1 a

-- | The labels in a Row.
type family Labels (r :: Row a) where
  Labels (R '[]) = '[]
  Labels (R (l :-> a ': xs)) = l ': Labels (R xs)

-- | Return a list of the labels in a record type.
labels :: forall ρ c s. (IsString s, Forall ρ c) => [s]
labels = getConst $ metamorph @ρ @c @(Const ()) @(Const [s]) @(Const ()) Proxy (const $ Const []) doUncons doCons (Const ())
  where doUncons _ _ = (Const (), Const ())
        doCons l _ (Const c) = Const $ show' l : c



{--------------------------------------------------------------------
  Common operations on types over rows
--------------------------------------------------------------------}
-- | Extendable row types support adding labels to the row.
class Extendable (t :: Row * -> *) where
  type Inp t a
  -- | Record extension. The row must not already contain the label.
  extend  :: forall a l r. (KnownSymbol l,r .\ l) => Label l -> Inp t a -> t r -> t (Extend l a r)

-- | Updatable row types support changing the value at a label in the row.
class Updatable (t :: Row * -> *) where
  -- Update the value in the Row at the given label by providing a new one.
  update :: KnownSymbol l => Label l -> r .! l -> t r -> t r

-- | Focusable row types support modifying the value at a label in the row,
-- and doing it in a lens-y way
class Focusable (t :: Row * -> *) where
  type FRequires t :: (* -> *) -> Constraint
  -- Apply the given function to the value in the Row at the given label.
  focus :: (FRequires t f, KnownSymbol l) => Label l -> (r .! l -> f a) -> t r -> f (t (Modify l a r))

-- | Renamable row types support renaming labels in the row.
class Renamable (t :: Row * -> *) where
  -- Rename a label in the row.
  rename :: (KnownSymbol l, KnownSymbol l', r .\ l') => Label l -> Label l' -> t r -> t (Rename l l' r)

-- | Eraseable row types can be folded up.  Really, this should be called RowFoldable
--   or something, and the inner functions should be
--   @forall a. c a => a -> Output t b -> Output t b@
--   with a base case value of @Output t b@ provided, and then 'erase' can be derived
--   from that.
class Erasable (t :: Row * -> *) where
  -- | The output structure of the fold
  type Output t a
  -- | The output structure of the zip fold
  type OutputZip t a
  -- | A standard fold
  erase :: Forall r c => Proxy c -> (forall a. c a => a -> b) -> t r -> Output t b
  -- A fold with labels
  eraseWithLabels :: (Forall r c, IsString s) => Proxy c -> (forall a. c a => a -> b) -> t r -> Output t (s, b)
  -- | A fold over two row type structures at once
  eraseZip :: Forall r c => Proxy c -> (forall a. c a => a -> a -> b) -> t r -> t r -> OutputZip t b



{--------------------------------------------------------------------
  Convenient type families and classes
--------------------------------------------------------------------}

-- | A kind to give nicer error messages than Bool
data Unique = LabelUnique Symbol | LabelNotUnique Symbol

-- | Are all of the labels in this Row unique?
class AllUniqueLabels r
instance AllUniqueLabels (R '[])
instance ((R r) .\ l, AllUniqueLabels (R r)) => AllUniqueLabels (R (l :-> a ': r))

-- | Are the two rows disjoint? (i.e. their sets of labels are disjoint)
class Disjoint x y
instance {-# INCOHERENT #-} Disjoint (R '[]) y
instance {-# INCOHERENT #-} Disjoint x (R '[])
instance {-# INCOHERENT #-} (Disjoint (R x) y, y .\ l) => Disjoint (R (l :-> a ': x)) y
instance {-# INCOHERENT #-} (Disjoint x (R y), x .\ l) => Disjoint x (R (l :-> a ': y))

-- | Is the first row a subset of the second?
class Subset x y
instance Subset (R '[]) y
instance (HasType l a y, Subset (R x) y) => Subset (R (l :-> a ': x)) y

-- | Map a type level function over a Row.
type family Map (f :: a -> b) (r :: Row a) :: Row b where
  Map f (R r) = R (MapR f r)

type family MapR (f :: a -> b) (r :: [LT a]) :: [LT b] where
  MapR f '[] = '[]
  MapR f (l :-> v ': t) = l :-> f v ': MapR f t

-- | Zips two rows together to create a Row of the pairs.
--   The two rows must have the same set of labels.
type family RZip (r1 :: Row *) (r2 :: Row *) where
  RZip (R r1) (R r2) = R (ZipR r1 r2)

type family ZipR (r1 :: [LT *]) (r2 :: [LT *]) where
  ZipR '[] '[] = '[]
  ZipR (l :-> t1 ': r1) (l :-> t2 ': r2) =
    l :-> (t1, t2) ': ZipR r1 r2

type family Inject (l :: LT *) (r :: [LT *]) where
  Inject (l :-> t) '[] = (l :-> t ': '[])
  Inject (l :-> t) (l' :-> t' ': x) =
      Ifte (l <=.? l')
      (l :-> t   ': l' :-> t' ': x)
      (l' :-> t' ': Inject (l :-> t)  x)

type family Ifte (c :: Bool) (t :: k) (f :: k)   where
  Ifte True  t f = t
  Ifte False t f = f

data NoSuchField (s :: Symbol)

type family Get (l :: Symbol) (r :: [LT *]) where
  Get l '[] = NoSuchField l
  Get l (l :-> t ': x) = t
  Get l (l' :-> t ': x) = Get l x

type family Remove (l :: Symbol) (r :: [LT *]) where
  Remove l (l :-> t ': x) = x
  Remove l (l' :-> t ': x) = l' :-> t ': Remove l x

type family LacksP (l :: Symbol) (r :: Row *) where
  LacksP l (R r) = LacksR l r

type family LacksR (l :: Symbol) (r :: [LT *]) where
  LacksR l '[] = LabelUnique l
  LacksR l (l :-> t ': x) = LabelNotUnique l
  LacksR l (p ': x) = LacksR l x

-- | Useful for checking if a symbol is *not* in the symbol list.
type family LacksL (l :: Symbol) (ls :: [Symbol]) where
  LacksL l '[] = LabelUnique l
  LacksL l (l ': x) = LabelNotUnique l
  LacksL l (p ': x) = LacksL l x

type family Merge (l :: [LT *]) (r :: [LT *]) where
  Merge '[] r = r
  Merge l '[] = l
  Merge (h :-> a ': tl)   (h :-> a ': tr) =
      (h :-> a ': Merge tl tr)
  Merge (hl :-> al ': tl) (hr :-> ar ': tr) =
      Ifte (hl <=.? hr)
      (hl :-> al ': Merge tl (hr :-> ar ': tr))
      (hr :-> ar ': Merge (hl :-> al ': tl) tr)

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


