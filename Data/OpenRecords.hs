{-# LANGUAGE TypeOperators, ScopedTypeVariables,GADTs, KindSignatures, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TypeFamilies, ViewPatterns, DataKinds, ConstraintKinds, UndecidableInstances,FunctionalDependencies,RankNTypes,AllowAmbiguousTypes, InstanceSigs, PolyKinds, TypeApplications #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords
-- Copyright   :  (c) Atze van der Ploeg 2013
-- License     :  BSD-style
-- Maintainer  :  atzeus@gmail.org
-- Stability   :  expirimental
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


module Data.OpenRecords

 (
             -- * Types and constraints
             Label(..),
             KnownSymbol(..),
             Rec,   Row,
             -- * Construction
             empty,Empty ,
             -- ** Extension
             extend, extendUnique, Extend,
             -- ** Renaming
             rename, renameUnique, Rename,
             -- ** Restriction
             (.-), (:-), 
             -- ** Update
             update,
             -- * Query
             (.!), (:!),
             -- * Focus
             focus, Modify,
             -- * Combine
             -- ** Union
              (.++), (:++),
             -- ** Disjoint union
              (.+) , (:+),
             -- * Row constraints
             (:\), Disjoint, Labels, Forall(..),
             -- * Row only operations
             -- * Syntactic sugar
             RecOp(..), RowOp(..), (.|), (:|),
             -- * Labels
             labels



           
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
import Data.String (IsString (fromString))
import GHC.TypeLits
import GHC.Exts -- needed for constraints kinds
import Data.Proxy
import Data.Type.Equality (type (==))
import Unconstrained


-- | A label 
data Label (s :: Symbol) = Label

instance KnownSymbol s => Show (Label s) where
  show = symbolVal




{--------------------------------------------------------------------
  Row constraints
--------------------------------------------------------------------}

-- | Does the row lack (i.e. it has not) the specified label?

type r :\ l = (LacksP l r ~ LabelUnique l)
-- | Are the two rows disjoint? (i.e. their sets of labels are disjoint)
type Disjoint l r = (DisjointR l r ~ IsDisjoint)




-- private things for row operations



{--------------------------------------------------------------------
  Open records
--------------------------------------------------------------------}

data HideType where
  HideType :: a -> HideType

-- | A record with row r.
data Rec (r :: Row *) where
  OR :: HashMap String (Seq HideType) -> Rec r

-- | The kind of rows. This type is only used as a datakind. A row is a typelevel entity telling us 
--   which symbols are associated with which types.
newtype Row a = R [LT a] -- constructor not exported

-- | The empty record
empty :: Rec Empty
empty = OR M.empty

-- | Type level variant of 'empty'
type family Empty :: Row * where
  Empty = R '[]

{--------------------------------------------------------------------
  Basic record operations
--------------------------------------------------------------------}


-- | Record extension. The row may already contain the label, 
--   in which case the origin value can be obtained after restriction ('.-') with
--   the label.
extend :: KnownSymbol l => Label l -> a -> Rec r -> Rec (Extend l a r)  
extend (show -> l) a (OR m) = OR $ M.insert l v m 
   where v = HideType a <| M.lookupDefault S.empty l m

-- | Record extension without shadowing. The row may not already contain label l.
extendUnique :: (KnownSymbol l,r :\ l) => Label l -> a -> Rec r -> Rec (Extend l a r)   
extendUnique = extend

-- | Type level operations of 'extend' and 'extendUnique'
type family Extend (l :: Symbol) (a :: *) (r :: Row *) :: Row * where
  Extend l a (R x) = R (Inject (l :-> a) x)

-- | Update the value associated with the label.
update :: KnownSymbol l => Label l -> r :! l -> Rec r -> Rec r
update (show -> l) a (OR m) = OR $ M.adjust f l m where f = S.update 0 (HideType a)  

type family Modify (l :: Symbol) (a :: *) (r :: Row *) :: Row * where
  Modify l a (R ρ) = R (ModifyR l a ρ)

type family ModifyR (l :: Symbol) (a :: *) (ρ :: [LT *]) :: [LT *] where
  ModifyR l a (l :-> a' ': ρ) = l :-> a ': ρ
  ModifyR l a (l' :-> a' ': ρ) = l' :-> a' ': ModifyR l a ρ

-- | Focus on the value associated with the label.
focus :: (Functor f, KnownSymbol l) => Label l -> (r :! l -> f a) -> Rec r -> f (Rec (Modify l a r))
focus (show -> l) f r@(OR m) = case S.viewl (m M.! l) of HideType x :< v -> OR . flip (M.insert l) m . (<| v) . HideType <$> f (unsafeCoerce x)

-- | Rename a label. The row may already contain the new label , 
--   in which case the origin value can be obtained after restriction ('.-') with
--   the new label.
rename :: (KnownSymbol l, KnownSymbol l') => Label l -> Label l' -> Rec r -> Rec (Rename l l' r)
rename l l' r = extend l' (r .! l) (r .- l)

-- | Rename a label. The row may not already contain the new label.
renameUnique :: (KnownSymbol l, KnownSymbol l', r :\ l') => Label l -> Label l' -> Rec r -> Rec (Rename l l' r)
renameUnique = rename

-- | Type level operation of  'rename' and 'renameUnique'
type family Rename (l :: Symbol) (l' :: Symbol) (r :: Row *) :: Row * where
  Rename l l' r = Extend  l' (r :! l) (r :- l)

infix  8 .-
-- | Record selection
(.!) :: KnownSymbol l => Rec r -> Label l -> r :! l
(OR m) .! (show -> a) = x'
   where x S.:< t =  S.viewl $ m M.! a 
         -- notice that this is safe because of the external type
         x' = case x of HideType p -> unsafeCoerce p 



infixl 6 :!
-- | Type level operation of '.!'
type family (r :: Row *) :! (t :: Symbol) :: * where
  (R r) :! l = Get l r

-- | Record restriction. Delete the label l from the record.
(.-) :: KnownSymbol l =>  Rec r -> Label l -> Rec (r :- l)
(OR m) .- (show -> a) = OR m'
   where x S.:< t =  S.viewl $ m M.! a 
         m' = case S.viewl t of
               EmptyL -> M.delete a m
               _      -> M.insert a t m

-- | Type level operation of '.-'
type family (r :: Row *) :- (s :: Symbol)  :: Row * where
  (R r) :- l = R (Remove l r)



-- | Record union (not commutative)
(.++) :: Rec l -> Rec r -> Rec (l :++ r)
(OR l) .++ (OR r) = OR $ M.unionWith (><) l r

-- | Type level operation of '.++'
type family (l :: Row *) :++  (r :: Row *)  :: Row * where
  (R l) :++ (R r) = R (Merge l r)

-- | Record disjoint union (commutative)
(.+) :: Disjoint l r => Rec l -> Rec r -> Rec (l :+ r)
(OR l) .+ (OR r) = OR $ M.unionWith (error "Impossible") l r

-- | Type level operation of '.+'
type family (l :: Row *) :+  (r :: Row *)  :: Row * where
  (R l) :+ (R r) = R (Merge l r)

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


infix 5 :=
infix 5 :!=
infix 5 :<-

-- | Here we provide a datatype for denoting record operations. Use '.|' to
--   actually apply the operations.
-- 
--   This allows us to chain operations with nicer syntax.
--   For example we can write:
--
-- > p :<-| z .| y :<- 'b' .| z :!= False .| x := 2 .| y := 'a' .| empty
-- 
-- Which results in:
-- 
-- > { p=False, x=2, y='b' }
-- 
-- Without this sugar, we would have written it like this:
--
-- >  rename z p $ update y 'b' $ extendUnique z False $ extend x 2 $ extend y 'a' empty
--
-- 
--  [@:<-@] Record update. Sugar for 'update'.
--
--  [@:=@] Record extension. Sugar for 'extend'.
--
--  [@:!=@] Record extension, without shadowing. Sugar for 'extendUnique'.
--
--  [@:<-|@] Record label renaming. Sugar for 'rename'.
--
--  [@:<-!@] Record label renaming. Sugar for 'renameUnique'.
data RecOp (c :: Row * -> Constraint) (rowOp :: RowOp *) where
  (:<-)  :: KnownSymbol l           => Label l -> a      -> RecOp (HasType l a) RUp
  (:=)   :: KnownSymbol l           => Label l -> a      -> RecOp Unconstrained1 (l ::= a)  
  (:!=)  :: KnownSymbol l => Label l -> a      -> RecOp (Lacks l) (l ::= a)  
  (:<-|) :: (KnownSymbol l, KnownSymbol l') => Label l' -> Label l -> RecOp Unconstrained1 (l' ::<-| l)
  (:<-!) :: (KnownSymbol l, KnownSymbol l', r :\ l') => Label l' -> Label l -> RecOp (Lacks l') (l' ::<-| l)



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

-- | Apply an operation to a record.
infixr 4 .|
(.|) :: c r => RecOp c ro -> Rec r -> Rec (ro :| r)
(l :<- a)   .| m  = update l a m
(l := a)    .| m  = extend l a m
(l :!= a)   .| m  = extendUnique l a m
(l' :<-| l) .| m  = rename l l' m
(l' :<-! l) .| m  = renameUnique l l' m

-- | Apply a (typelevel) operation to a row. Type level operation of '.|'
infixr 4 :|
type family (x :: RowOp *) :| (r :: Row *)  :: Row * where
  RUp          :| r = r
  (l ::= a)    :| r = Extend l a r
  (l' ::<-| l) :| r = Rename l l' r

{--------------------------------------------------------------------
  Constrained record operations
--------------------------------------------------------------------}



type family Labels (r :: Row a) where
  Labels (R '[]) = '[]
  Labels (R (l :-> a ': xs)) = l ': Labels (R xs)


-- | If the constaint @c@ holds for all elements in the row @r@,
--  then the methods in this class are available.
class Forall (r :: Row *) (c :: * -> Constraint) where
  -- | Given a default value @a@, where@a@ can be instantiated to each type in the row,
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

labels :: forall r s . (Forall r Unconstrained1, IsString s) => Proxy r -> [s]
labels _ = getConst $ rinitAWithLabel @r (Proxy @Unconstrained1) (Const . pure . show')

class RowMap (f :: * -> *) (r :: Row *) where
  type Map f r :: Row *
  rmap :: Proxy f -> (forall a.  a -> f a) -> Rec r -> Rec (Map f r)
  rsequence :: Applicative f => Proxy f -> Rec (Map f r) -> f (Rec r)

instance RowMapx f r => RowMap f (R r) where
  type Map f (R r) = R (RM f r)
  rmap = rmap'
  rsequence = rsequence'

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

class RowMapC (c :: * -> Constraint) (f :: * -> *) (r :: Row *) where
  type MapC c f r :: Row *
  rmapc :: Proxy c -> Proxy f -> (forall a. c a => a -> f a) -> Rec r -> Rec (MapC c f r)

instance RMapc c f r => RowMapC c f (R r) where
  type MapC c f (R r) = R (RMapp c f r)
  rmapc = rmapc'

class RMapc (c :: * -> Constraint) (f :: * -> *) (r :: [LT *]) where
  type RMapp c f r :: [LT *]
  rmapc' :: Proxy c -> Proxy f -> (forall a. c a => a -> f a) -> Rec (R r) -> Rec (R (RMapp c f r))

instance RMapc c f '[] where
  type RMapp c f '[] = '[]
  rmapc' _ _ _ _ = empty

instance (KnownSymbol l, c v, RMapc c f t) => RMapc c f (l :-> v ': t) where
  type RMapp c f (l :-> v ': t) = l :-> f v ': RMapp c f t
  rmapc' c w f r = unsafeInjectFront l (f (r .! l)) (rmapc' c w f (r .- l))
    where l = Label :: Label l

instance Forall (R '[]) c where
  rinit _ _ = empty
  rinitAWithLabel _ _ = pure empty
  eraseWithLabels _ _ _ = []
  eraseToHashMap _ _ _ = M.empty
  eraseZip _ _ _ _ = []

instance (KnownSymbol l, Forall (R t) c, c a) => Forall (R (l :-> a ': t)) c where
  rinit c f = unsafeInjectFront l f (rinit c f) where l = Label :: Label l

  rinitAWithLabel c f = unsafeInjectFront l <$> f l <*> rinitAWithLabel c f where l = Label :: Label l

  eraseWithLabels c f r =
    (show' l, f (r .! l)) : eraseWithLabels c f (r .- l) where l = Label :: Label l

  eraseToHashMap c f r =
    M.insert (show' l) (f (r .! l)) $ eraseToHashMap c f (r .- l) where l = Label :: Label l

  eraseZip c f x y = (f (x .! l) (y .! l)) : eraseZip c f (x .- l) (y .- l) where
    l = Label :: Label l

show' :: (IsString s, Show a) => a -> s
show' = fromString . show

class RowZip (r1 :: Row *) (r2 :: Row *) where
  type RZip r1 r2 :: Row *
  rzip :: Rec r1 -> Rec r2 -> Rec (RZip r1 r2)
  
instance RZipt r1 r2 => RowZip (R r1) (R r2) where
  type RZip (R r1) (R r2) = R (RZipp r1 r2)
  rzip = rzip'

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

-- some standard type classes

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

unsafeInjectFront :: KnownSymbol l => Label l -> a -> Rec (R r) -> Rec (R (l :-> a ': r))
unsafeInjectFront (show -> a) b (OR m) = OR $ M.insert a v m
  where v = HideType b <| M.lookupDefault S.empty a m


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


-- | there doesn't seem to be a (<=.?) :: Symbol -> Symbol -> Bool,
-- so here it is in terms of other ghc-7.8 type functions
type a <=.? b = (CmpSymbol a b == 'LT)
