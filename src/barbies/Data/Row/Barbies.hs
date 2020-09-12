{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Row.Barbie
--
-- This module adds Barbie instances for 'Rec' and 'Var'.
--
-----------------------------------------------------------------------------


module Data.Row.Barbies () where

import           Data.Functor.Compose
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Row
import           Data.Row.Dictionaries
import qualified Data.Row.Records      as Rec
import qualified Data.Row.Variants     as Var

import           Data.Functor.Barbie (FunctorB(..), TraversableB(..), DistributiveB(..), ApplicativeB(..), ConstraintsB(..))
import qualified Barbies.Constraints as B

-- | Barbies requires that the functor be the final argument of the type.  So,
-- even though the real type is @Rec (Map f ρ)@, we must wrap it in a newtype
-- wrapper so that 'f' is at the end.
newtype BarbieRec (ρ :: Row *) (f :: * -> *) = BarbieRec { unBarbieRec :: Rec (Rec.Map f ρ) }
newtype BarbieVar (ρ :: Row *) (f :: * -> *) = BarbieVar { unBarbieVar :: Var (Var.Map f ρ) }

instance FreeForall r => FunctorB (BarbieRec r) where
  bmap f = BarbieRec . Rec.transform' @r f . unBarbieRec

instance FreeForall r => TraversableB (BarbieRec r) where
  btraverse :: forall e f g. Applicative e => (forall a. f a -> e (g a)) -> BarbieRec r f -> e (BarbieRec r g)
  btraverse f  = fmap BarbieRec . Rec.traverseMap @Unconstrained1 @e @f @g @r f . unBarbieRec

instance FreeForall r => DistributiveB (BarbieRec r) where
  bdistribute :: forall f g. Functor f => f (BarbieRec r g) -> BarbieRec r (Compose f g)
  bdistribute = BarbieRec . Rec.compose @f @g @r . Rec.distribute @f @(Rec.Map g r) . fmap unBarbieRec
    \\ freeForall @(Rec.Map g r) @(IsA Unconstrained1 g) \\ mapForall @g @r @Unconstrained1

instance (AllUniqueLabels r, FreeForall r) => ApplicativeB (BarbieRec r) where
  bpure :: forall f. (forall a. f a) -> BarbieRec r f
  bpure fa = BarbieRec $ runIdentity $ Rec.fromLabelsMapA @Unconstrained1 @Identity @f @r (const $ Identity fa)

  bprod :: forall f g. BarbieRec r f -> BarbieRec r g -> BarbieRec r (f `Product` g)
  bprod (BarbieRec r1) (BarbieRec r2) = BarbieRec $ Rec.zipTransform @Unconstrained1 @r @f @g @(Product f g) Pair r1 r2

instance FreeForall r => ConstraintsB (BarbieRec r) where
  type AllB c (BarbieRec r) = Forall r c
  baddDicts :: forall c f. Forall r c => BarbieRec r f -> BarbieRec r (B.Dict c `Product` f)
  baddDicts = BarbieRec . Rec.transform @c @r @f @(B.Dict c `Product` f) (Pair (B.Dict @c)) . unBarbieRec



instance FreeForall r => FunctorB (BarbieVar r) where
  bmap f = BarbieVar . Var.transform' @r f . unBarbieVar

instance FreeForall r => TraversableB (BarbieVar r) where
  btraverse :: forall e f g. Applicative e => (forall a. f a -> e (g a)) -> BarbieVar r f -> e (BarbieVar r g)
  btraverse f  = fmap BarbieVar . Var.traverseMap @Unconstrained1 @e @f @g @r f . unBarbieVar

instance FreeForall r => ConstraintsB (BarbieVar r) where
  type AllB c (BarbieVar r) = Forall r c
  baddDicts :: forall c f. Forall r c => BarbieVar r f -> BarbieVar r (B.Dict c `Product` f)
  baddDicts = BarbieVar . Var.transform @c @r @f @(B.Dict c `Product` f) (Pair (B.Dict @c)) . unBarbieVar
