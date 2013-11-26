{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables,GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies, ViewPatterns, DataKinds, ConstraintKinds, UndecidableInstances,FunctionalDependencies,RankNTypes,MagicHash #-}

module OpenRecVar(Label(..),LeadsTo(..), List(..),LabelLt,Get, Inject,Remove,OpenRec, empty, (.|), (.+),(!), (.-)) where

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

infixr 5 :=
data LeadsTo a b = a := b deriving Show

data Label (s :: Symbol) = Label

instance Show (Label s) where
  show Label = symbolVal :: s

instance Typeable (Label s) where
  typeRep# _ = mkTyCon3 "OpenRecVar" "OpenRecVar" ("Label:" ++ (symbolVal :: s))



type family LabelLt (a :: *) (b :: *) :: Bool where
  LabelLt (Label s) (Label t) = s <=.? t

type family Ifte (c :: Bool) (t :: List (LeadsTo * *)) (f :: List (LeadsTo * *)) where
  Ifte True  t f = t
  Ifte False t f = f

type family Inject (l :: *) (t :: *) (r :: List (LeadsTo * *)) :: List (LeadsTo * *) where
  Inject l t Nil = (l := t ::: Nil)
  Inject l t (l' := t' ::: x) = Ifte (LabelLt l l')
                                (l := t   ::: l' := t' ::: x)
                                (l' := t' ::: Inject l t x)

type family Overwrite (l :: *) (t :: *) (r :: List (LeadsTo * *)) :: List (LeadsTo * *) where
  Overwrite l t Nil              = (l := t ::: Nil)
  Overwrite l t (l := t' ::: x)  = l := t ::: x
  Overwrite l t (l' := t' ::: x) = Ifte (LabelLt l l')
                                   (l := t   ::: l' := t' ::: x)
                                   (l' := t' ::: Overwrite l t x)

type family Get (t :: *) (r :: List (LeadsTo * *)) :: * where
  Get t (t := v ::: r) = v
  Get t (t' := v' ::: r) = Get t r

type family Remove (t :: *) (r :: List (LeadsTo * *)) :: List (LeadsTo * *) where
  Remove t (t := v ::: r) = r
  Remove t (t' := v' ::: r) = t' := v' ::: Remove t r

{-
data OpenVar (m :: List (LeadsTo * *))  where
  OV :: (Typeable l) => l -> t -> OpenVar m -- Constructor not exported

inj :: (Typeable l, (Get l m)~t) => l -> t -> OpenVar m
inj = OV

prj :: forall l m t m'. (Typeable l, (Get l m)~t) => l -> OpenVar m -> Maybe t
prj _ (OV l t) = case (cast l :: Maybe l) of
   Just _ -> Just $ unsafeCoerce t
   Nothing -> Nothing
-}

data HideType where
  HideType :: a -> HideType

data OpenRec (m :: List (LeadsTo * *)) where
  OR :: Map TypeRep (Seq HideType) -> OpenRec m

empty :: OpenRec Nil
empty = OR M.empty

infixr 4 .+
infix  9  !
infix  9 .-

infixr 4 .|

(.+) :: Typeable a => LeadsTo a b -> OpenRec m -> OpenRec (Inject a b m)
((typeOf -> a) := b) .+ (OR m) = OR $ M.insert a v m
  where v = HideType b <| M.findWithDefault S.empty a m

(.|) :: Typeable a => LeadsTo a b -> OpenRec m -> OpenRec (Overwrite a b m)
((typeOf -> a) := b) .| (OR m) = OR $ M.insert a v m
  where l = M.findWithDefault S.empty a m
        v = case viewl l of
             EmptyL -> HideType b <| l
             _ :< t -> HideType b <| t
             
(!) :: OpenRec m -> Label a -> Get a m
(OR m) ! (typeOf -> a) = x'
   where x S.:< t =  S.viewl $ m M.! a 
         x' = case x of
               HideType p -> unsafeCoerce p

(.-) ::  OpenRec m -> Label a -> OpenRec (Remove a m)
(OR m) .- (typeOf -> a) = OR m'
   where x S.:< t =  S.viewl $ m M.! a 
         m' = case S.viewl t of
               EmptyL -> M.delete a m
               _      -> M.insert a t m

class ToHetList m x | m -> x, x -> m where
  toHetList :: OpenRec m -> HetList x
  fromHetList :: HetList x -> OpenRec m
 
instance ToHetList Nil Nil where
  toHetList _ = HetNil
  fromHetList _ = empty

instance (ToHetList m x,Inject l t m ~ (l := t ::: m)) => 
          ToHetList (l := t ::: m) (LeadsTo l t ::: x) where
  toHetList m = l := m ! l :> toHetList (m .- l)
    where l = (Label :: l)
  fromHetList (l := a :> t)  = l := a .+ fromHetList t


instance (ToHetList m x, Forall Show x) => Show (OpenRec m) where
  show m = "{ " ++ meat ++ " }"
    where meat = intercalate ", " $ show' $ hl
          toSt = erase ::  (forall a. Show a => a -> b) -> HetList x -> [b]
          show' = toSt show :: HetList x -> [String]
          hl = toHetList m :: HetList x


