{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds, RankNTypes, DataKinds #-}
{-# LANGUAGE DeriveDataTypeable,TypeFamilies, ViewPatterns, DataKinds, ConstraintKinds #-}
module Examples where
import Prelude hiding ((.))



import Data.Typeable

import OpenRecVar

infix 9 .
(.) ::  Typeable a => OpenRec m -> a -> Get a m
(.) = (!)

origin :: OpenRec (X := Double ::: Y := Double ::: Nil)
origin =  X := (10 :: Double) .| Y := (0 :: Double) .| empty
-- want to write : origin = { x = 0 , y = 0 }

-- want to write : origin3 = {  z = 0 | origin }
origin3 = Z := 0 .| origin

origin2 :: OpenRec (X := Double ::: Y := Double ::: Nil)
origin2 = Y := (0 :: Double) .| X := (0 :: Double) .| empty


vec = X := (3 :: Double) .| Y := (4 :: Double) .| X := "Bla" .| empty

vec2 = X := (3 :: Double) .+ Y := (4 :: Double) .| X := "Bla" .| empty

-- Inferred Type
distance
  :: (Floating t, OpenRecVar.Get X m ~ t, OpenRecVar.Get Y m ~ t) =>
     OpenRec m -> OpenRecVar.Get Y m
distance r = sqrt $ r.X*r.X + r.Y*r.Y

move r d = X := r.X + d.X .| Y := r.Y + d.Y .| r



data X = X deriving (Typeable, Show)
instance Label X where getLabel = X

data Y = Y deriving (Typeable, Show)
instance Label Y where getLabel = Y

data Z = Z deriving (Typeable, Show)
instance Label Z where getLabel = Z

data P = P deriving (Typeable, Show)
instance Label P where getLabel = P

data Q = Q deriving (Typeable, Show)
instance Label Q where getLabel = Q


type instance LabelLt X X = True
type instance LabelLt X Y = True
type instance LabelLt X Z = True
type instance LabelLt X P = True
type instance LabelLt X Q = True

type instance LabelLt Y X = False
type instance LabelLt Y Y = True
type instance LabelLt Y Z = True
type instance LabelLt Y P = True
type instance LabelLt Y Q = True

type instance LabelLt Z X = False
type instance LabelLt Z Y = False
type instance LabelLt Z Z = True
type instance LabelLt Z P = True
type instance LabelLt Z Q = True

type instance LabelLt P X = False
type instance LabelLt P Y = False
type instance LabelLt P Z = False
type instance LabelLt P P = True
type instance LabelLt Q Q = True

type instance LabelLt Q X = False
type instance LabelLt Q Y = False
type instance LabelLt Q Z = False
type instance LabelLt Q P = False
type instance LabelLt Q Q = True
