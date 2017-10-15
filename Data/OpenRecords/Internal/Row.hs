-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Internal.Row
--
-- This module implements the internals of open records and variants.
--
-----------------------------------------------------------------------------


module Data.OpenRecords.Internal.Row
  (
  -- * Rec and Var
    Rec(..), Var(..)
  -- * Common operations on types over rows
  , Extendable(..)
  , Updatable(..)
  , Focusable(..)
  , Renamable(..)
  -- * SHOULDN'T BE HERE
  , empty, (.!), (.-), impossible, trial
  -- * Rows
  , Label(..)
  , KnownSymbol(..)
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
  , Forall(..)
  , RowMap(..), RowMapC(..), RowMapCF(..)
  , RowZip(..)
  )
where

import Data.Functor.Const
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import Data.Sequence(Seq,viewl,ViewL(..),(><),(<|))
import qualified Data.HashMap.Lazy as M
import qualified Data.Sequence as S
import Unsafe.Coerce
import Data.List
import Data.Maybe (fromMaybe)
import Data.String (IsString (fromString))
import GHC.TypeLits
import GHC.Exts -- needed for constraints kinds
import Data.Proxy
import Data.Type.Equality (type (==))
import Unconstrained



{--------------------------------------------------------------------
  Record and Variant definitions
--------------------------------------------------------------------}
-- Ideally, this file would only include Row stuff, but because 'Forall' and
-- 'Switch' (and any others?) are not
-- generic enough,relying on both 'Rec' and 'Var', they must be defined here
-- so they can be shared.  Thus, 'Rec' and 'Var' must be here as well.

-- | A record with row r.
data Rec (r :: Row *) where
  OR :: HashMap String (Seq HideType) -> Rec r

instance (Forall r Show) => Show (Rec r) where
  show r = "{ " ++ intercalate ", " binds ++ " }"
    where binds = (\ (x, y) -> x ++ "=" ++ y) <$> eraseWithLabels (Proxy @Show) show r

instance (Forall r Eq) => Eq (Rec r) where
  r == r' = and $ eraseZip (Proxy @Eq) (==) r r'

instance (Eq (Rec r), Forall r Ord) => Ord (Rec r) where
  compare m m' = cmp $ eraseZip (Proxy @Ord) compare m m'
      where cmp l | [] <- l' = EQ
                  | a : _ <- l' = a
                  where l' = dropWhile (== EQ) l

instance (Forall r Bounded) => Bounded (Rec r) where
  minBound = rinit (Proxy @Bounded) minBound
  maxBound = rinit (Proxy @Bounded) maxBound


-- | The variant type.
data Var (r :: Row *) where
  OneOf :: (String, HideType) -> Var r

instance Forall r Show => Show (Var r) where
  show v = (\ (x, y) -> "{" ++ x ++ "=" ++ y ++ "}") $ eraseVWithLabel (Proxy @Show) show v

instance Forall r Eq => Eq (Var r) where
  r == r' = fromMaybe False $ eraseVZip (Proxy @Eq) (==) r r'


--
{--------------------------------------------------------------------
  Common operations on types over rows
--------------------------------------------------------------------}
class Extendable (t :: Row * -> *) where
  type Inp t a
  -- Extend the Row by adding the given input for the given label.
  extend  :: forall l a r. KnownSymbol l => Label l -> Inp t a -> t r -> t (Extend l a r)
  extendUnique :: forall l a r. (KnownSymbol l,r :\ l) => Label l -> Inp t a -> t r -> t (Extend l a r)
  extendUnique = extend @t @l @a

instance Extendable Rec where
  type Inp Rec a = a
  extend (show -> l) a (OR m) = OR $ M.insert l v m
     where v = HideType a <| M.lookupDefault S.empty l m

instance Extendable Var where
  type Inp Var a = Proxy a
  extend _ _ (OneOf (l, x)) = OneOf (l, x)


class Updatable (t :: Row * -> *) where
  -- Update the value in the Row at the given label by providing a new one.
  update :: KnownSymbol l => Label l -> r :! l -> t r -> t r

instance Updatable Rec where
  update (show -> l) a (OR m) = OR $ M.adjust f l m where f = S.update 0 (HideType a)

instance Updatable Var where
  update (show -> l') a (OneOf (l, x)) = OneOf (l, if l == l' then HideType a else x)


class Focusable (t :: Row * -> *) where
  -- Apply the given function to the value in the Row at the given label.
  focus :: (Applicative f, KnownSymbol l) => Label l -> (r :! l -> f a) -> t r -> f (t (Modify l a r))

instance Focusable Rec where
  focus (show -> l) f r@(OR m) = case S.viewl (m M.! l) of HideType x :< v -> OR . flip (M.insert l) m . (<| v) . HideType <$> f (unsafeCoerce x)

instance Focusable Var where
  focus (show -> l') f (OneOf (l, HideType x)) = if l == l' then (OneOf . (l,) . HideType) <$> f (unsafeCoerce x) else pure (OneOf (l, HideType x))


class Renamable (t :: Row * -> *) where
  -- Rename the given label in the Row to the new given label.
  rename :: (KnownSymbol l, KnownSymbol l') => Label l -> Label l' -> t r -> t (Rename l l' r)
  renameUnique :: (KnownSymbol l, KnownSymbol l', r :\ l') => Label l -> Label l' -> t r -> t (Rename l l' r)
  renameUnique = rename

instance Renamable Rec where
  rename l l' r = extend l' (r .! l) (r .- l)

instance Renamable Var where
  rename (show -> l1) (show -> l2) (OneOf (l, x)) = OneOf (if l == l1 then l2 else l, x)


{--------------------------------------------------------------------
  SHOULD BE REMOVED
--------------------------------------------------------------------}
-- | The empty record
empty :: Rec Empty
empty = OR M.empty

-- | Record selection
(.!) :: KnownSymbol l => Rec r -> Label l -> r :! l
OR m .! (show -> a) = x'
   where x S.:< t =  S.viewl $ m M.! a
         -- notice that this is safe because of the external type
         x' = case x of HideType p -> unsafeCoerce p



infix  8 .-
-- | Record restriction. Delete the label l from the record.
(.-) :: KnownSymbol l =>  Rec r -> Label l -> Rec (r :- l)
OR m .- (show -> a) = OR m'
   where x S.:< t =  S.viewl $ m M.! a
         m' = case S.viewl t of
               EmptyL -> M.delete a m
               _      -> M.insert a t m

-- | Convert a variant into either the value at the given label or a variant without
-- that label.  This is the basic variant destructor.
trial :: KnownSymbol l => Var r -> Label l -> Either (r :! l) (Var (r :- l))
trial (OneOf (l, HideType x)) (show -> l') = if l == l' then Left (unsafeCoerce x) else Right (OneOf (l, HideType x))

-- | A Variant with no options is uninhabited.
impossible :: Var Empty -> a
impossible _ = error "Impossible! Somehow, a variant of nothing was produced."

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
  Constrained record operations
--------------------------------------------------------------------}

-- | The labels in a Row.
type family Labels (r :: Row a) where
  Labels (R '[]) = '[]
  Labels (R (l :-> a ': xs)) = l ': Labels (R xs)

-- | Get a list of label names from a Row.
labels :: forall r s . (Forall r Unconstrained1, IsString s) => Proxy r -> [s]
labels _ = getConst $ rinitAWithLabel @r (Proxy @Unconstrained1) (Const . pure . show')



-- | If the constaint @c@ holds for all elements in the row @r@,
--  then the methods in this class are available.
--
-- TODO: Make this class generic.  It should have a small number (one?) of generic
-- operations (fold?, unfold?, map??) that are not specialized to e.g. Rec or Var.
-- Then, each of these functions would be standalone (but would require newtypes
-- due to Haskell's lack of type-level lambdas).
-- It may also use an associated type or open type family.  Not sure.
class Forall (r :: Row *) (c :: * -> Constraint) where
  -- | Given a default value @a@, where @a@ can be instantiated to each type in the row,
  -- create a new record in which all elements carry this default value.
  rinit     :: Proxy c -> (forall a. c a => a) -> Rec r
  rinitA    :: Applicative p => Proxy c -> (forall a. c a => p a) -> p (Rec r)
  rinitA proxy f = rinitAWithLabel proxy (pure f)
  rinitAWithLabel :: Applicative p => Proxy c -> (forall l a. (KnownSymbol l, c a) => Label l -> p a) -> p (Rec r)
  -- | Given a function @(a -> b)@ where @a@ can be instantiated to each type in the row,
  --   apply the function to each element in the record and collect the result in a list.
  erase    :: Proxy c -> (forall a. c a => a -> b) -> Rec r -> [b]
  erase proxy f = fmap (snd @String) . eraseWithLabels proxy f
  eraseWithLabels :: IsString s => Proxy c -> (forall a. c a => a -> b) -> Rec r -> [(s, b)]
  eraseToHashMap :: (IsString s, Eq s, Hashable s) =>
                    Proxy c -> (forall a . c a => a -> b) -> Rec r -> HashMap s b
  -- | Given a function @(a -> a -> b)@ where @a@ can be instantiated to each type of the row,
  -- apply the function to each pair of values that can be obtained by indexing the two records
  -- with the same label and collect the result in a list.
  eraseZip :: Proxy c -> (forall a. c a => a -> a -> b) -> Rec r -> Rec r -> [b]

  -- | Given a function @(a -> b)@ where @a@ can be instantiated to each type in the row,
  --   apply the function to the element in the variant.
  eraseV    :: Proxy c -> (forall a. c a => a -> b) -> Var r -> b
  eraseV proxy f = (snd @String) . eraseVWithLabel proxy f
  -- | A version of 'eraseV' that also provides the label.
  eraseVWithLabel :: IsString s => Proxy c -> (forall a. c a => a -> b) -> Var r -> (s, b)
  -- | Given a function @(a -> a -> b)@ where @a@ can be instantiated to each type of the row,
  -- apply the function to the two values within the two variants assuming that each are in
  -- the same field.
  eraseVZip :: Proxy c -> (forall a. c a => a -> a -> b) -> Var r -> Var r -> Maybe b

instance Forall (R '[]) c where
  rinit _ _ = empty
  rinitAWithLabel _ _ = pure empty
  eraseWithLabels _ _ _ = []
  eraseToHashMap _ _ _ = M.empty
  eraseZip _ _ _ _ = []
  eraseVWithLabel _ _ = impossible
  eraseVZip _ _ _ = impossible

instance (KnownSymbol l, Forall (R t) c, c a) => Forall (R (l :-> a ': t)) c where
  rinit c f = unsafeInjectFront l f (rinit c f) where l = Label :: Label l

  rinitAWithLabel c f = unsafeInjectFront l <$> f l <*> rinitAWithLabel c f where l = Label :: Label l

  eraseWithLabels c f r =
    (show' l, f (r .! l)) : eraseWithLabels c f (r .- l) where l = Label :: Label l

  eraseToHashMap c f r =
    M.insert (show' l) (f (r .! l)) $ eraseToHashMap c f (r .- l) where l = Label :: Label l

  eraseZip c f x y = f (x .! l) (y .! l) : eraseZip c f (x .- l) (y .- l) where
    l = Label :: Label l

  eraseVWithLabel c f v = case trial v l of
    Left  x  -> (show' l, f x)
    Right v' -> eraseVWithLabel c f v'
    where l = Label :: Label l

  eraseVZip c f x y = case (trial x l, trial y l) of
    (Left a,  Left b)  -> Just $ f a b
    (Right x, Right y) -> eraseVZip c f x y
    _ -> Nothing
    where l = Label :: Label l


-- | A class for mapping a function over a record.
-- TODO: Can this be made more generic?
class RowMap (f :: * -> *) (r :: Row *) where
  type Map f r :: Row *
  rmap :: Proxy f -> (forall a.  a -> f a) -> Rec r -> Rec (Map f r)
  rsequence :: Applicative f => Proxy f -> Rec (Map f r) -> f (Rec r)

instance RowMapx f r => RowMap f (R r) where
  type Map f (R r) = R (RM f r)
  rmap = rmap'
  rsequence = rsequence'

-- | A helper class for mapping a function over a record.
-- TODO: Can this be made more generic?
class RowMapx (f :: * -> *) (r :: [LT *]) where
  type RM f r :: [LT *]
  rmap' :: Proxy f -> (forall a.  a -> f a) -> Rec (R r) -> Rec (R (RM f r))
  rsequence' :: Applicative f => Proxy f -> Rec (R (RM f r)) -> f (Rec (R r))

instance RowMapx f '[] where
  type RM f '[] = '[]
  rmap' _ _ _ = empty
  rsequence' _ _ = pure empty

instance (KnownSymbol l,  RowMapx f t) => RowMapx f (l :-> v ': t) where
  type RM f (l :-> v ': t) = l :-> f v ': RM f t
  rmap' w f r = unsafeInjectFront l (f (r .! l)) (rmap' w f (r .- l))
    where l = Label :: Label l
  rsequence' w r = unsafeInjectFront l <$> r .! l <*> rsequence' w (r .- l)
    where l = Label :: Label l


-- | A class for mapping a function over a record where each element of the record
-- satisfies a constraint.
-- TODO: Can this be made more generic?
class RowMapCF (c :: * -> Constraint) (f :: * -> *) (r :: Row *) where
  type MapCF c f r :: Row *
  rmapcf :: Proxy c -> Proxy f -> (forall a. c a => a -> f a) -> Rec r -> Rec (MapCF c f r)

instance RMapcf c f r => RowMapCF c f (R r) where
  type MapCF c f (R r) = R (RMappf c f r)
  rmapcf = rmapcf'

-- | A helper class for mapping a function over a record where each element of the record
-- satisfies a constraint.
-- TODO: Can this be made more generic?
class RMapcf (c :: * -> Constraint) (f :: * -> *) (r :: [LT *]) where
  type RMappf c f r :: [LT *]
  rmapcf' :: Proxy c -> Proxy f -> (forall a. c a => a -> f a) -> Rec (R r) -> Rec (R (RMappf c f r))

instance RMapcf c f '[] where
  type RMappf c f '[] = '[]
  rmapcf' _ _ _ _ = empty

instance (KnownSymbol l, c v, RMapcf c f t) => RMapcf c f (l :-> v ': t) where
  type RMappf c f (l :-> v ': t) = l :-> f v ': RMappf c f t
  rmapcf' c w f r = unsafeInjectFront l (f (r .! l)) (rmapcf' c w f (r .- l))
    where l = Label :: Label l


-- | A class for mapping a function over a record where each element of the record
-- satisfies a constraint and the types don't change.
-- TODO: Can this be made more generic?
class RowMapC (c :: * -> Constraint) (r :: Row *) where
  type MapC c r :: Row *
  rmapc :: Proxy c -> (forall a. c a => a -> a) -> Rec r -> Rec (MapC c r)

instance RMapc c r => RowMapC c (R r) where
  type MapC c (R r) = R (RMapp c r)
  rmapc = rmapc'

-- | A class for mapping a function over a record where each element of the record
-- satisfies a constraint and the types don't change.
-- TODO: Can this be made more generic?
class RMapc (c :: * -> Constraint) (r :: [LT *]) where
  type RMapp c r :: [LT *]
  rmapc' :: Proxy c -> (forall a. c a => a -> a) -> Rec (R r) -> Rec (R (RMapp c r))

instance RMapc c '[] where
  type RMapp c '[] = '[]
  rmapc' _ _ _ = empty

instance (KnownSymbol l, c v, RMapc c t) => RMapc c (l :-> v ': t) where
  type RMapp c (l :-> v ': t) = l :-> v ': RMapp c t
  rmapc' c f r = unsafeInjectFront l (f (r .! l)) (rmapc' c f (r .- l))
    where l = Label :: Label l


-- | A class for zipping two records together.
-- TODO: Can this be made more generic?
class RowZip (r1 :: Row *) (r2 :: Row *) where
  type RZip r1 r2 :: Row *
  rzip :: Rec r1 -> Rec r2 -> Rec (RZip r1 r2)

instance RZipt r1 r2 => RowZip (R r1) (R r2) where
  type RZip (R r1) (R r2) = R (RZipp r1 r2)
  rzip = rzip'

-- | A helper class for zipping two records together.
-- TODO: Can this be made more generic?
class RZipt (r1 :: [LT *]) (r2 :: [LT *]) where
  type RZipp r1 r2 :: [LT *]
  rzip' :: Rec (R r1) -> Rec (R r2) -> Rec (R (RZipp r1 r2))

instance RZipt '[] '[] where
  type RZipp '[] '[] = '[]
  rzip' _ _ = empty

instance (KnownSymbol l, RZipt t1 t2) =>
   RZipt (l :-> v1 ': t1) (l :-> v2 ': t2) where

   type RZipp (l :-> v1 ': t1) (l :-> v2 ': t2) = l :-> (v1,v2) ': RZipp t1 t2
   rzip' r1 r2 = unsafeInjectFront l (r1 .! l, r2 .! l) (rzip' (r1 .- l) (r2 .- l))
       where l = Label :: Label l

-- | A helper function for unsafely adding an element to the front of a record
unsafeInjectFront :: KnownSymbol l => Label l -> a -> Rec (R r) -> Rec (R (l :-> a ': r))
unsafeInjectFront (show -> a) b (OR m) = OR $ M.insert a v m
  where v = HideType b <| M.lookupDefault S.empty a m

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


