{-# LANGUAGE TypeOperators, NoMonomorphismRestriction, ScopedTypeVariables,GADTs, KindSignatures, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TypeFamilies, ViewPatterns, DataKinds, ConstraintKinds, UndecidableInstances,FunctionalDependencies,RankNTypes,AllowAmbiguousTypes, InstanceSigs, PolyKinds #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  OpenRecVar
-- Copyright   :  (c) Atze van der Ploeg 2013
-- License     :  BSD-style
-- Maintainer  :  atzeus@gmail.org
-- Stability   :  expirimental
-- 
-- This module implements extensible records using closed type famillies.
--
-- See Examples.hs for examples.
-- 
-- For this a small extension to GHC is needed which implements the 
-- built-in closed type family 
--  @type family (m :: Symbol) <=.? (n :: Symbol) :: Bool@
-- where Symbol is a type literal.
--
-- Patches to implement this extension to GHC (patchmain) and the base library (patchlib) are also found in the 
-- git repo that hosts this project <https://github.com/atzeus/openrec>
-- I've sent these patches to Iavor Diatchki (who is implementing the type literal stuff) to get these (small) changes into the main repo.
--
-- This small extension allows us to keep lists of (label,type) pairs sorted thereby ensuring
-- that { x = 0, y = 0 } and { y = 0, x = 0 } have the same type.
-- 
-- In this way we can implement standard type classes such as Show, Eq, Ord and Bounded
-- for open records, given that all the elements of the open record satify the constraint.
--
-- 
-- Now uses Hashmaps because of speed <http://blog.johantibell.com/2012/03/announcing-unordered-containers-02.html>
-----------------------------------------------------------------------------


module Records

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
             -- * Combine
             -- ** Union
              (.++), (:++),
             -- ** Disjoint union
              (.+) , (:+),
             -- * Row constraints
             (:\), Disjoint, Forall(..), CWit,
             -- * Syntactic sugar
             RecOp(..), RowOp(..), (.|), (:|)



           
     ) 
where

import Data.HashMap.Lazy(HashMap)
import Data.Sequence(Seq,viewl,ViewL(..),(><),(<|))
import qualified Data.HashMap.Lazy as M
import qualified Data.Sequence as S
import Unsafe.Coerce
import Data.List
import GHC.TypeLits
import GHC.Exts -- needed for constraints kinds


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


-- | Record extension. The row may already contain label, 
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
(.+) :: (l :\\ r) => Rec l -> Rec r -> Rec (l :+ r)
(OR l) .+ (OR r) = OR $ M.unionWith (error "Impossible") l r

-- | Type level operation of '.+'
type family (l :: Row *) :+  (r :: Row *)  :: Row * where
  (R l) :+ (R r) = R (Merge l r)

{--------------------------------------------------------------------
  Syntactic sugar for record operations
--------------------------------------------------------------------}
-- | A constraint not constraining anything
class NoConstr (a :: Row *)
instance NoConstr a

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
  (:=)   :: KnownSymbol l           => Label l -> a      -> RecOp NoConstr (l ::= a)  
  (:!=)  :: KnownSymbol l => Label l -> a      -> RecOp (Lacks l) (l ::= a)  
  (:<-|) :: (KnownSymbol l, KnownSymbol l') => Label l' -> Label l -> RecOp NoConstr (l' ::<-| l)
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

-- | A witness of a constraint. For use like this @rinit (CWit :: CWit Bounded) minBound@
data CWit (c :: * -> Constraint) = CWit

-- | If the constaint @c@ holds for all elements in the row @r@,
--  then the methods in this class are available.
class Forall (r :: Row *) (c :: * -> Constraint) where
  -- | Given a default value @a@, where@a@ can be instantiated to each type in the row,
  -- create a new record in which all elements carry this default value.
  rinit     :: CWit c -> (forall a. c a => a) -> Rec r
  -- | Given a function @(a -> b)@ where @a@ can be instantiated to each type in the row,
  --   apply the function to each element in the record and collect the result in a list.

  erase    :: CWit c -> (forall a. c a => a -> b) -> Rec r -> [(String,b)]
  -- | Given a function @(a -> a -> b)@ where @a@ can be instantiated to each type of the row,
  -- apply the function to each pair of values that can be obtained by indexing the two records
  -- with the same label and collect the result in a list.

  eraseZip :: CWit c -> (forall a. c a => a -> a -> b) -> Rec r -> Rec r -> [(String,b)]

instance Forall (R '[]) c where
  rinit _ _ = empty
  erase _ _ _ = []
  eraseZip _ _ _ _ = []

instance (KnownSymbol l, Forall (R t) c, c a) => Forall (R (l :-> a ': t)) c where
  rinit c f = unsafeInjectFront l f (rinit c f) where l = Label :: Label l

  erase c f r = (show l,f (r .! l)) : erase c f (r .- l) where l = Label :: Label l

  eraseZip c f x y = (show l, f (x .! l) (y .! l)) : eraseZip c f (x .- l) (y .- l) where
    l = Label :: Label l
  
-- some standard type classes

instance (Forall r Show) => Show (Rec r) where
  show r = "{ " ++ meat ++ " }"
    where meat = intercalate ", " binds
          binds = map (\(x,y) -> x ++ "=" ++ y) vs
          vs = erase (CWit :: CWit Show) show r

instance (Forall r Eq) => Eq (Rec r) where
  r == r' = and $ map snd $ eraseZip (CWit :: CWit Eq) (==) r r'

instance (Eq (Rec r), Forall r Ord) => Ord (Rec r) where
  compare m m' = cmp $ map snd $ eraseZip (CWit :: CWit Ord) compare m m'
      where cmp l | [] <- l' = EQ
                  | a : _ <- l' = a
                  where l' = dropWhile (== EQ) l


instance (Forall r Bounded) => Bounded (Rec r) where
  minBound = rinit (CWit :: CWit Bounded) minBound
  maxBound = rinit (CWit :: CWit Bounded) maxBound

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

type family Get (l :: Symbol) (r :: [LT *]) where
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

