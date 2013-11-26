{-# LANGUAGE TypeOperators, NoMonomorphismRestriction, ScopedTypeVariables,GADTs, KindSignatures, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TypeFamilies, ViewPatterns, DataKinds, ConstraintKinds, UndecidableInstances,FunctionalDependencies,Rank2Types,AllowAmbiguousTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  OpenRecVar
-- Copyright   :  (c) Atze van der Ploeg 2013
-- License     :  BSD-style
-- Maintainer  :  atzeus@gmail.org
-- Stability   :  expirimental
-- 
-- This module implements extensible records and variants as 
-- described in paper "Extensible Records with Scoped Labels",
-- Daan Leijen, Proc. 2005 Symp. Trends in Functional Programming
-- available at <http://research.microsoft.com/pubs/65409/scopedlabels.pdf>
--
-- See Examples.hs for examples.
-- 
-- The main difference with the paper is that this module does not extend
-- the type system, but instead uses closed type families, GADTs and
-- type level symbols to implement the system. 
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
-- Using multiparam type classes, we can convert open records to heterogeneous lists of values 
-- labels. In the Hetrogenous list module, we provide the type class Forall c l
-- which allows some operations given that the constraint c (using constraintkinds) holds
-- for all elements of the list. 
-- 
-- In this way we can implement standard type classes such as Show, Eq, Ord and Bounded
-- for open records, given that all the elements of the open record satify the constraint.
--
-- For open variants, we need to specify the actual type of the variant
-- at the use site @inj :: forall a b m. KnownSymbol a => Label a -> b -> OpenVar (Inject a b m)@
-- Hence this module requires AllowAmbigousTypes.
-- 
-----------------------------------------------------------------------------


module OpenRecVar (

             -- * Labels
             KnownSymbol(..),
             Label(..),
             IsSingleton(..),
             -- * Row operations
             Inject, Get, Remove,
             -- * Open records

             OpenRec,   
             empty,
             LeadsTo(..),
             (!),
             (.|),
             (.-),
             update,
             ToHetList(..),
             -- * Open variants
            OpenVar,
            inj,
            embed,
            decomp
     ) where

import Data.Typeable
import Data.Map(Map,unionWith)
import Data.Sequence(Seq,viewl,ViewL(..),(><),(<|))
import qualified Data.Map as M
import qualified Data.Sequence as S
import Unsafe.Coerce
import HetList 
import Data.List
import GHC.TypeLits
import Data.Typeable.Internal

{--------------------------------------------------------------------
  Labels
--------------------------------------------------------------------}

-- | A label 
data Label (s :: Symbol) = Label

class IsSingleton l where 
  getVal :: l
instance IsSingleton (Label l) where
  getVal = Label

instance KnownSymbol s => Show (Label s) where
  show = symbolVal


{--------------------------------------------------------------------
  Row operations
--------------------------------------------------------------------}

type family LabelLt (a :: *) (b :: *) :: Bool where
  LabelLt (Label s) (Label t) = s <=.? t

type family Ifte (c :: Bool) (t :: List (LeadsTo Symbol *)) (f :: List (LeadsTo Symbol *)) where
  Ifte True  t f = t
  Ifte False t f = f

-- | Inject a symbol (l) type (t) pair into a (sorted) list of such pairs
--   Afterwards, the resulting list is again sorted.
type family Inject (l :: Symbol) (t :: *) (r :: List (LeadsTo Symbol *)) :: List (LeadsTo Symbol *) where
  Inject l t Nil = (l := t ::: Nil)
  Inject l t (l' := t' ::: x) = Ifte (l <=.? l')
                                (l := t   ::: l' := t' ::: x)
                                (l' := t' ::: Inject l t x)
-- | Get the type associated with a label
type family Get (t :: Symbol) (r :: List (LeadsTo Symbol *)) :: * where
  Get t (t := v ::: r) = v
  Get t (t' := v' ::: r) = Get t r

-- | Remove a label from a list of label-type pairs
type family Remove (t :: Symbol) (r :: List (LeadsTo Symbol *)) :: List (LeadsTo Symbol *) where
  Remove t (t := v ::: r) = r
  Remove t (t' := v' ::: r) = t' := v' ::: Remove t r

{--------------------------------------------------------------------
  Open records
--------------------------------------------------------------------}

data HideType where
  HideType :: a -> HideType

-- | Openrecord type
data OpenRec (m :: List (LeadsTo Symbol *)) where
  OR :: Map String (Seq HideType) -> OpenRec m

-- | The empty record
empty :: OpenRec Nil
empty = OR M.empty


infixr 5 :=
-- | Just a nice way to denote an label value pair.
data LeadsTo a b = a := b deriving Show

infix  9  !
infix  9 .-

infixr 4 .|

-- | Record extension
(.|) :: KnownSymbol a => LeadsTo (Label a) b -> OpenRec m -> OpenRec (Inject a b m)
((show -> a) := b) .| (OR m) = OR $ M.insert a v m
  where v = HideType b <| M.findWithDefault S.empty a m


-- | Record selection
(!) :: KnownSymbol a => OpenRec m -> Label a -> Get a m
(OR m) ! (show -> a) = x'
   where x S.:< t =  S.viewl $ m M.! a 
         x' = case x of
               HideType p -> unsafeCoerce p

-- | Record restriction
(.-) :: KnownSymbol a =>  OpenRec m -> Label a -> OpenRec (Remove a m)
(OR m) .- (show -> a) = OR m'
   where x S.:< t =  S.viewl $ m M.! a 
         m' = case S.viewl t of
               EmptyL -> M.delete a m
               _      -> M.insert a t m

-- | Record update
update :: KnownSymbol a =>  Label a -> Get a m -> OpenRec m -> OpenRec m
update l v (OR m) = OR $ M.adjust f (show l) m
  where f = S.update 0 (HideType v)  

-- Conversion to and from Hetrogenous lists

class ToHetList (m :: List (LeadsTo Symbol *)) (l :: List *) (x :: List *) | m -> l x, l x -> m where
  values :: OpenRec m -> HetList x
  labels    :: OpenRec m -> HetList l
  fromHetList :: HetList l -> HetList x -> OpenRec m
 
instance ToHetList Nil Nil Nil where
  values _     = HetNil
  labels _        = HetNil
  fromHetList _ _ = empty

instance (KnownSymbol l, ToHetList m lt x,Inject l t m ~ (l := t ::: m)) => 
          ToHetList (l := t ::: m) (Label l ::: lt) (t ::: x) where
  values m = m ! l :> values (m .- l)     where l = (Label :: Label l)
  labels m = l     :> labels (m .- l)        where l = (Label :: Label l)
  fromHetList (l :> tl) (v :> tv) = l := v .| fromHetList tl tv 

-- some standard type classes

instance (ToHetList m l x, Forall l Show, Forall x Show) => Show (OpenRec m) where
  show m = "{ " ++ meat ++ " }"
    where meat = intercalate ", " binds
          binds = zipWith (\x y -> x ++ "=" ++ y) ls vs
          ls = toStl show (labels m)
          vs = toStv show (values m)
          -- i don't know exactly why this explicit typing is needed...
          toStl = erase ::  (forall a. Show a => a -> String) -> HetList l -> [String]
          toStv = erase ::  (forall a. Show a => a -> String) -> HetList x -> [String]

instance (ToHetList m l x, Forall x Eq) => Eq (OpenRec m) where
  m == m' = and $ eqt (==) (values m) (values m')
      where -- i don't know exactly why this explicit typing is needed...
            eqt = eraseZip ::  (forall a. Eq a => a -> a -> Bool) -> HetList x -> HetList x -> [Bool]

instance (ToHetList m l x, Forall x Eq, Forall x Ord) => Ord (OpenRec m) where
  compare m m' = cmp $ eqt compare (values m) (values m')
      where -- i don't know exactly why this explicit typing is needed...
            eqt = eraseZip ::  (forall a. Ord a => a -> a -> Ordering) -> HetList x -> HetList x -> [Ordering]
            cmp l | [] <- l' = EQ
                  | a : _ <- l' = a
                  where l' = dropWhile (== EQ) l

instance (ToHetList m l x, Forall l IsSingleton, Forall x Bounded) => Bounded (OpenRec m) where
  minBound = fromHetList (hinitl getVal) (hinitv minBound)
       where hinitl = hinit :: (forall a. IsSingleton a => a) -> HetList l
             hinitv = hinit :: (forall a. Bounded a => a) -> HetList x
  maxBound = fromHetList (hinitl getVal) (hinitv maxBound)
       where hinitl = hinit :: (forall a. IsSingleton a => a) -> HetList l
             hinitv = hinit :: (forall a. Bounded a => a) -> HetList x
     
{--------------------------------------------------------------------
  Open variants
--------------------------------------------------------------------}

-- | Variant type
data OpenVar (m :: List (LeadsTo Symbol *))  where
  OV :: String -> Int -> t -> OpenVar m -- Constructor not exported

-- | Variant injection
inj :: forall a b m. KnownSymbol a => Label a -> b -> OpenVar (Inject a b m)
inj (show -> a) b = OV a 0 b


-- | Variant embedding
embed :: forall a b m . KnownSymbol a => Label a -> OpenVar m -> OpenVar (Inject a b m)
embed (show -> l) (OV s i t) 
  | l == s    = OV s (i + 1) t
  | otherwise = OV s i t

-- | Variant decomposition
decomp :: KnownSymbol a => Label a -> OpenVar m -> (Either (Get a m) (OpenVar (Remove a m)))
decomp (show -> a) (OV l i t) 
  | l == a    = if i == 0 
                then Left  $ unsafeCoerce t 
                else Right $ OV l (i - 1) t
  | otherwise      = Right $ OV l i t
                            




