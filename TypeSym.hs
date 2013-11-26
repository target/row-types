{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables,GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies, ViewPatterns, DataKinds, ConstraintKinds, UndecidableInstances,FunctionalDependencies,RankNTypes,MagicHash #-}

module TestSym where
import GHC.TypeLits


data PS (i :: Symbol) = PS

data PN (i :: Nat) = PN

data PB (b :: Bool) = PB

bla :: PN j -> PN i -> PB (j <=? i)
bla PN PN = PB

blas :: PS j -> PS i -> PB (j <=.? i)
blas PS PS = PB

get :: (PB True) -> Int
get _ = 3
