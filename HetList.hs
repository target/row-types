{-# LANGUAGE ScopedTypeVariables,GADTs, DataKinds, FlexibleContexts ,TypeOperators,ConstraintKinds, MultiParamTypeClasses, KindSignatures, RankNTypes, FlexibleInstances, InstanceSigs, UndecidableInstances #-}

module HetList where
import GHC.Exts

infixr 4 :::
data List a = a ::: List a | Nil

infixr 4 :>

data HetList a where
  HetNil :: HetList Nil
  (:>)   :: h -> HetList t -> HetList (h ::: t)


class Forall (c :: * -> Constraint) (l :: List *) where
  erase :: (forall a. c a => a -> b) -> HetList l -> [b]

instance Forall c Nil where
  erase f HetNil = []

instance (c h, Forall c t) => Forall c (h ::: t) where
  erase :: (forall a. c a => a -> b) -> HetList (h ::: t) -> [b]
  erase f (h :> t) = f h : deep f t
     where deep = erase  ::  (forall a. c a => a -> b) -> HetList t -> [b]

