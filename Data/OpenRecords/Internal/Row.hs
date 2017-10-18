-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Internal.Row
--
-- This module implements the internals of open records and variants.
--
-----------------------------------------------------------------------------


module Data.OpenRecords.Internal.Row
  (
  -- * Rows
    Row(..)
  , Label(..)
  , KnownSymbol
  , LT(..)
  , Empty
  , HideType(..)
  -- * Row Operations
  , (:\), Disjoint, Subset, Complement, Extend, Modify, Rename
  , (:!), (:-), (:+)
  , Lacks, HasType
  , RowOp(..), (:|)
  -- * Row Classes
  , Labels, labels
  , ValOf, RowPair(..)
  , Forall(..)
  , Unconstrained1
  -- * Common operations on types over rows
  , Extendable(..)
  , Updatable(..)
  , Focusable(..)
  , Renamable(..)
  , Erasable(..)
  -- * Helper functions
  , show'
  , LacksL, Unique(..), AllUniqueLabels
  )
where

import Data.Functor.Const
import Data.Proxy
import Data.String (IsString (fromString))
import Data.Type.Equality (type (==))

import GHC.TypeLits
import GHC.Exts -- needed for constraints kinds




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

-- | Does the row lack (i.e. it has not) the specified label?
type r :\ l = (LacksP l r ~ LabelUnique l)
-- | Are the two rows disjoint? (i.e. their sets of labels are disjoint)
type Disjoint l r = (DisjointR l r ~ IsDisjoint)


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
  Rename l l' r = Extend  l' (r :! l) (r :- l)

infixl 6 :!
-- | Type level label fetching
type family (r :: Row *) :! (t :: Symbol) :: * where
  R r :! l = Get l r

-- | Type level Row element removal
type family (r :: Row *) :- (s :: Symbol)  :: Row * where
  R r :- l = R (Remove l r)

-- | Type level Row append (to be used when Rows are disjoint)
type family (l :: Row *) :+  (r :: Row *)  :: Row * where
  R l :+ R r = R (Merge l r)


{--------------------------------------------------------------------
  Syntactic sugar for record operations
--------------------------------------------------------------------}
-- | Alias for ':\'. It is a class rather than an alias, so that
--   it can be partially appliced.
class (r :\ l) => Lacks (l :: Symbol) (r :: Row *)
instance (r :\ l) => Lacks l r


-- | Alias for @(r :! l) ~ a@. It is a class rather than an alias, so that
--   it can be partially appliced.
class ((r :! l) ~ a ) => HasType l a r
instance ((r :! l) ~ a ) => HasType l a r

-- | Type level datakind corresponding to 'RecOp'.
--   Here we provide a datatype for denoting row operations. Use ':|' to
--   actually apply the type level operation.
--
--   This allows us to chain type level operations with nicer syntax.
--   For example we can write:
--
-- > "p" ::<-| "z" :| RUp :| "z" ::= Bool :| "x" ::= Double :| "y" ::= Char :| Empty
--
-- As the type of the expression:
--
-- > p :<-| z .| y :<- 'b' .| z :!= False .| x := 2 .| y := 'a' .| empty
--
-- Without this sugar, we would have written it like this:
--
-- >  Rename "p" "z" (Extend "z" Bool (Extend x Double (Extend "x" Int Empty)))
--
-- Of course, we can also just write:
--
-- > "p" ::= Bool :| "x" ::= Double :| "y" ::= Int :|  Empty
--
-- instead, doing the computation ourselves, or even let the type infer.
--
--  [@RUp@] Type level equivalent of ':<-'. Is the identity Row Operation.
--
--  [@::=@] Type level equivalent of ':='. Row extension. Sugar for 'Extend'.
--
--  [@::<-|@] Type level equivalent of ':<-|'. Row label renaming. Sugar for 'Rename'.
infix 5 ::=
infix 5 ::<-|
data RowOp (a :: *) where
  RUp      :: RowOp a
  (::=)    :: Symbol -> a -> RowOp a
  (::<-|)   :: Symbol -> Symbol -> RowOp a


-- | Apply a (typelevel) operation to a row. Type level operation of '.|'
infixr 4 :|
type family (x :: RowOp *) :| (r :: Row *)  :: Row * where
  RUp          :| r = r
  (l ::= a)    :| r = Extend l a r
  (l' ::<-| l) :| r = Rename l l' r




{--------------------------------------------------------------------
  Constrained record operations
--------------------------------------------------------------------}

-- | ValOf is used internally by 'Forall' to determine the intermediate value
--   between the fold and unfold values of 'metamorph'.
type family ValOf (f :: Row * -> *) (τ :: *) :: *
type instance ValOf (Const x) τ = x

-- | Any structure over a row in which every element is similarly constrained can
--   be metamorphized into another structure over the same row.
class Forall (r :: Row *) (c :: * -> Constraint) where
  -- | A metamorphism is an unfold followed by a fold.
  metamorph :: forall (f :: Row * -> *) (g :: Row * -> *).
               (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => f ('R (ℓ :-> τ ': ρ)) -> (ValOf f τ, f ('R ρ)))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => ValOf f τ -> g ('R ρ) -> g ('R (ℓ :-> τ ': ρ)))
               -- ^ The fold
            -> f r  -- ^ The input structure
            -> g r

instance Forall (R '[]) c where
  metamorph empty _ _ = empty

instance (KnownSymbol ℓ, c τ, Forall ('R ρ) c) => Forall ('R (ℓ :-> τ ': ρ)) c where
  metamorph empty uncons cons r = cons t $ metamorph @('R ρ) @c empty uncons cons r'
    where (t, r') = uncons r

-- | A null constraint
class Unconstrained1 a
instance Unconstrained1 a

-- | The labels in a Row.
type family Labels (r :: Row a) where
  Labels (R '[]) = '[]
  Labels (R (l :-> a ': xs)) = l ': Labels (R xs)

-- | Return a list of the labels in a record type.
labels :: forall ρ c s. (IsString s, Forall ρ c) => Proxy ρ -> [s]
labels _ = getConst $ metamorph @ρ @c @(Const ()) @(Const [s]) (const $ Const []) doUncons doCons (Const ())
  where doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Const () ('R (ℓ :-> τ ': ρ)) -> ((), Const () ('R ρ))
        doUncons _ = ((), Const ())
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => () -> Const [s] ('R ρ) -> Const [s] ('R (ℓ :-> τ ': ρ))
        doCons _ (Const c) = Const $ show' (Label @ℓ) : c


-- | A newtype for a pair of rows --- useful for functions involving 'metamorph'.
newtype RowPair (f :: Row * -> *) (ρ :: Row *) = RowPair { unRowPair :: (f ρ, f ρ) }
type instance ValOf (RowPair f) τ = (ValOf f τ, ValOf f τ)


{--------------------------------------------------------------------
  Common operations on types over rows
--------------------------------------------------------------------}
-- | Extendable row types support adding labels to the row.
class Extendable (t :: Row * -> *) where
  type Inp t a
  -- | Record extension. The row must not already contain the label.
  extend  :: forall l a r. (KnownSymbol l,r :\ l) => Label l -> Inp t a -> t r -> t (Extend l a r)

-- | Updatable row types support changing the value at a label in the row.
class Updatable (t :: Row * -> *) where
  -- Update the value in the Row at the given label by providing a new one.
  update :: KnownSymbol l => Label l -> r :! l -> t r -> t r

-- | Focusable row types support modifying the value at a label in the row,
-- and doing it in a lens-y way
class Focusable (t :: Row * -> *) where
  -- Apply the given function to the value in the Row at the given label.
  focus :: (Applicative f, KnownSymbol l) => Label l -> (r :! l -> f a) -> t r -> f (t (Modify l a r))

-- | Renamable row types support renaming labels in the row.
class Renamable (t :: Row * -> *) where
  -- Rename a label in the row.
  rename :: (KnownSymbol l, KnownSymbol l', r :\ l') => Label l -> Label l' -> t r -> t (Rename l l' r)

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

-- | A constraint that holds if the first Row is a subset of the second.
class Subset r r'
instance Subset (R '[]) r'
instance ((r' :! l) ~ a, Subset (R r) (r' :- l)) => Subset (R (l :-> a ': r)) r'

class AllUniqueLabels r
instance AllUniqueLabels (R '[])
instance ((R r) :\ l, AllUniqueLabels (R r)) => AllUniqueLabels (R (l :-> a ': r))

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

type family LacksL (l :: Symbol) (ls :: [Symbol]) where
  LacksL l '[] = LabelUnique l
  LacksL l (l ': x) = LabelNotUnique l
  LacksL l (p ': x) = LacksL l x

type family Merge (l :: [LT *]) (r :: [LT *]) where
  Merge '[] r = r
  Merge l '[] = l
  Merge (hl :-> al ': tl) (hr :-> ar ': tr) =
      Ifte (hl <=.? hr)
      (hl :-> al ': Merge tl (hr :-> ar ': tr))
      (hr :-> ar ': Merge (hl :-> al ': tl) tr)

-- A kind to give nicer error messages than Bool
data DisjointErr = IsDisjoint | Duplicate Symbol

type family IfteD (c :: Bool) (t :: DisjointErr) (f :: DisjointErr)   where
  IfteD True  t f = t
  IfteD False t f = f

type family DisjointR (l :: Row *) (r :: Row *) where
  DisjointR (R l) (R r) = DisjointZ l r

type family DisjointZ (l :: [LT *]) (r :: [LT *]) where
    DisjointZ '[] r = IsDisjoint
    DisjointZ l '[] = IsDisjoint
    DisjointZ (l :-> al ': tl) (l :-> ar ': tr) = Duplicate l
    DisjointZ (hl :-> al ': tl) (hr :-> ar ': tr) =
      IfteD (hl <=.? hr)
      (DisjointZ tl (hr :-> ar ': tr))
      (DisjointZ (hl :-> al ': tl) tr)

-- | The complement is the leftover.  So, the complement of @l@ and @r@ is
--   whatever is remaining after all of the elements of @r@ are removed from @l@.
type family Complement (l :: Row *) (r :: Row *) where
  Complement (R l) (R r) = R (ComplementR l r)

type family ComplementR (l :: [LT *]) (r :: [LT *]) where
  ComplementR '[] r = '[]
  ComplementR l '[] = l
  ComplementR (l :-> al ': tl) (l :-> al ': tr) = ComplementR tl tr
  ComplementR (hl :-> al ': tl) (hr :-> ar ': tr) =
    Ifte (hl <=.? hr)
    (hl :-> al ': ComplementR tl (hr :-> ar ': tr))
    (ComplementR (hl :-> al ': tl) tr)


-- | There doesn't seem to be a (<=.?) :: Symbol -> Symbol -> Bool,
-- so here it is in terms of other ghc-7.8 type functions
type a <=.? b = (CmpSymbol a b == 'LT)


