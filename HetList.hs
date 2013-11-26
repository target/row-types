{-# LANGUAGE NoMonomorphismRestriction,ScopedTypeVariables,GADTs, DataKinds, FlexibleContexts ,TypeOperators,ConstraintKinds, MultiParamTypeClasses, KindSignatures, RankNTypes, FlexibleInstances, InstanceSigs, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  OpenRecVar
-- Copyright   :  (c) Atze van der Ploeg 2013
-- License     :  BSD-style
-- Maintainer  :  atzeus@gmail.org
-- Stability   :  expirimental
-- Portability :  portable
-- Simple Hetrogenous lists using GADTs and DataKinds
-- 
-----------------------------------------------------------------------------


module HetList(List(..), HetList(..), Forall(..))  where
import GHC.Exts -- needed for constraints kinds


-- | Intended to be used as DataKind: Type level lists
infixr 4 :::
data List a = a ::: List a | Nil

-- | Heterogenous lists, the type argument has the list of types
infixr 4 :>
data HetList a where
  HetNil :: HetList Nil
  (:>)   :: h -> HetList t -> HetList (h ::: t)


-- | Implements a number of useful operations that
--   we can do if all the types in a heterogenous list
--   satify some constraint.
class Forall (l :: List *) (c :: * -> Constraint)  where
  hinit  :: (forall a. c a => a) -> HetList l
  erase :: (forall a. c a => a -> b) -> HetList l -> [b]
  eraseZip :: (forall a. c a => a -> a -> b) -> HetList l -> HetList l -> [b]

instance Forall Nil c  where
  hinit f = HetNil
  erase f HetNil = []
  eraseZip f HetNil HetNil = []

instance (c h, Forall t c) => Forall (h ::: t) c where
  hinit f = (f :: h) :> deep f
    where deep = hinit  ::  (forall a. c a => a) -> HetList t
  erase :: (forall a. c a => a -> b) -> HetList (h ::: t) -> [b]
  erase f (h :> t) = f h : deep f t
     where deep = erase  ::  (forall a. c a => a -> b) -> HetList t -> [b]
  eraseZip :: (forall a. c a => a -> a -> b) -> HetList (h ::: t) -> HetList (h ::: t) -> [b]
  eraseZip f (hl :> tl) (hr :> tr) = f hl hr : deep f tl tr
     where deep = eraseZip  ::  (forall a. c a => a -> a -> b) -> HetList t -> HetList t -> [b]
