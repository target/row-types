-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Internal.Row
--
-- This module implements the internals of open records and variants.
--
-----------------------------------------------------------------------------


module Data.OpenRecords.Internal.Row
  (
  -- * Common operations on types over rows
    Extendable(..)
  , Updatable(..)
  , Focusable(..)
  , Renamable(..)
  -- * Rows
  , Label(..)
  , KnownSymbol
  , LT(..)
  , Row(..)
  , Empty
  , HideType(..)
  -- * Row Operations
  , (:\), Disjoint, Subset, Complement, Extend, Modify, Rename
  , (:!), (:-), (:++), (:+)
  , Lacks, HasType
  , RowOp(..), (:|)
  -- * Row Classes
  , Labels, labels
  , ValOf, RowPair(..)
  , Forall(..)
  , Unconstrained1
  , Erasable(..)
  -- * Helper functions
  , show'
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
-- | A label
data Label (s :: Symbol) = Label

instance KnownSymbol s => Show (Label s) where
  show = symbolVal


-- | The kind of rows. This type is only used as a datakind. A row is a typelevel entity telling us
--   which symbols are associated with which types.
newtype Row a = R [LT a] -- constructor not exported

-- | Type level variant of 'empty'
type family Empty :: Row * where
  Empty = R '[]


data HideType where
  HideType :: a -> HideType



{--------------------------------------------------------------------
  Row operations
--------------------------------------------------------------------}

-- | Does the row lack (i.e. it has not) the specified label?
type r :\ l = (LacksP l r ~ LabelUnique l)
-- | Are the two rows disjoint? (i.e. their sets of labels are disjoint)
type Disjoint l r = (DisjointR l r ~ IsDisjoint)


class Subset r r'
instance Subset (R '[]) r'
instance (HasType l a r', Subset (R r) r') => Subset (R (l :-> a ': r)) r'


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
-- | Type level label fetching (type level '.!')
type family (r :: Row *) :! (t :: Symbol) :: * where
  R r :! l = Get l r

-- | Type level Row element removal (type level '.-')
type family (r :: Row *) :- (s :: Symbol)  :: Row * where
  R r :- l = R (Remove l r)

-- | Type level Row append (type level '.++')
type family (l :: Row *) :++  (r :: Row *)  :: Row * where
  R l :++ R r = R (Merge l r)

-- | Type level Row append to be used when Rows are disjoint (type level '.+')
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
  Common operations on types over rows
--------------------------------------------------------------------}
class Extendable (t :: Row * -> *) where
  type Inp t a
  -- | Record extension. The row may already contain the label.
  extend  :: forall l a r. KnownSymbol l => Label l -> Inp t a -> t r -> t (Extend l a r)
  -- | Record extension without shadowing. The row may not already contain label l.
  extendUnique :: forall l a r. (KnownSymbol l,r :\ l) => Label l -> Inp t a -> t r -> t (Extend l a r)
  extendUnique = extend @t @l @a

class Updatable (t :: Row * -> *) where
  -- Update the value in the Row at the given label by providing a new one.
  update :: KnownSymbol l => Label l -> r :! l -> t r -> t r

class Focusable (t :: Row * -> *) where
  -- Apply the given function to the value in the Row at the given label.
  focus :: (Applicative f, KnownSymbol l) => Label l -> (r :! l -> f a) -> t r -> f (t (Modify l a r))

class Renamable (t :: Row * -> *) where
  -- Rename a label. The row may already contain the new label.
  rename :: (KnownSymbol l, KnownSymbol l') => Label l -> Label l' -> t r -> t (Rename l l' r)
  -- | Rename a label. The row may not already contain the new label.
  renameUnique :: (KnownSymbol l, KnownSymbol l', r :\ l') => Label l -> Label l' -> t r -> t (Rename l l' r)
  renameUnique = rename


{--------------------------------------------------------------------
  Constrained record operations
--------------------------------------------------------------------}

type family ValOf (f :: Row * -> *) (τ :: *) :: *
type instance ValOf (Const x) τ = x

class Forall (r :: Row *) (c :: * -> Constraint) where
  -- foldRow :: forall (f :: Row * -> *).
  --            f Empty
  --         -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => f ('R ρ) -> f ('R (ℓ :-> τ ': ρ)))
  --         -> f r
  foldRow :: forall (f :: Row * -> *) (g :: Row * -> *).
             (f Empty -> g Empty)
          -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => f ('R (ℓ :-> τ ': ρ)) -> (ValOf f τ, f ('R ρ)))
          -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => ValOf f τ -> g ('R ρ) -> g ('R (ℓ :-> τ ': ρ)))
          -> f r
          -> g r

instance Forall (R '[]) c where
  foldRow empty _ _ = empty

instance (KnownSymbol ℓ, c τ, Forall ('R ρ) c) => Forall ('R (ℓ :-> τ ': ρ)) c where
  foldRow empty uncons cons r = cons t $ foldRow @('R ρ) @c empty uncons cons r'
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
labels _ = getConst $ foldRow @ρ @c @(Const ()) @(Const [s]) (const $ Const []) doUncons doCons (Const ())
  where doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ) => Const () ('R (ℓ :-> τ ': ρ)) -> ((), Const () ('R ρ))
        doUncons _ = ((), Const ())
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => () -> Const [s] ('R ρ) -> Const [s] ('R (ℓ :-> τ ': ρ))
        doCons _ (Const c) = Const $ show' (Label @ℓ) : c



newtype RowPair (f :: Row * -> *) (ρ :: Row *) = RowPair { unRowPair :: (f ρ, f ρ) }
type instance ValOf (RowPair f) τ = (ValOf f τ, ValOf f τ)

class Erasable (t :: Row * -> *) where
  type Output t a
  type OutputZip t a
  erase :: Forall r c => Proxy c -> (forall a. c a => a -> b) -> t r -> Output t b
  eraseWithLabels :: (Forall r c, IsString s) => Proxy c -> (forall a. c a => a -> b) -> t r -> Output t (s, b)
  eraseZip :: Forall r c => Proxy c -> (forall a. c a => a -> a -> b) -> t r -> t r -> OutputZip t b


-- | A helper function for showing labels
show' :: (IsString s, Show a) => a -> s
show' = fromString . show


{--------------------------------------------------------------------
  Convenient type families
--------------------------------------------------------------------}

data LT a = Symbol :-> a

-- gives nicer error message than Bool
data Unique = LabelUnique Symbol | LabelNotUnique Symbol

type family Inject (l :: LT *) (r :: [LT *]) where
  Inject (l :-> t) '[] = (l :-> t ': '[])
  Inject (l :-> t) (l' :-> t' ': x) =
      Ifte (l <=.? l')
      (l :-> t   ': l' :-> t' ': x)
      (l' :-> t' ': Inject (l :-> t)  x)

type family Ifte (c :: Bool) (t :: [LT *]) (f :: [LT *])   where
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

type family Merge (l :: [LT *]) (r :: [LT *]) where
  Merge '[] r = r
  Merge l '[] = l
  Merge (hl :-> al ': tl) (hr :-> ar ': tr) =
      Ifte (hl <=.? hr)
      (hl :-> al ': Merge tl (hr :-> ar ': tr))
      (hr :-> ar ': Merge (hl :-> al ': tl) tr)

-- gives nicer error message than Bool
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


-- | there doesn't seem to be a (<=.?) :: Symbol -> Symbol -> Bool,
-- so here it is in terms of other ghc-7.8 type functions
type a <=.? b = (CmpSymbol a b == 'LT)


