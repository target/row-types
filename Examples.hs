{-# LANGUAGE FlexibleContexts, ConstraintKinds,TypeOperators,DataKinds,DeriveDataTypeable, NoMonomorphismRestriction #-} 

module Examples where

import Data.Typeable
import OpenRecVar

data X = X deriving (Typeable, Show)
instance Label X
data Y = Y deriving (Typeable, Show)
instance Label Y
data Z = Z deriving (Typeable, Show)
instance Label Z
data Year = Year deriving (Typeable, Show)
instance Label Year

-- type can be inferred, but look much less nice because it does not place typeoperators infix
-- and explicitly mentions kinds:
{- origin
  :: OpenRec
       ((':::)
          (To * *)
          ((':->) * * X Double)
          ((':::) (To * *) ((':->) * * Y Double) ('N (To * *))))
-}
origin :: OpenRec (X :-> Double ::: Y :-> Double ::: N)
origin = X .-> (0 :: Double) +++ Y .-> (0 :: Double)

-- Inferred Type
distance :: (Floating a, GetType X m a, GetType Y m a) => OpenRec m -> a
distance r = sqrt $ r!X*r!X + r!Y*r!Y

test1 = distance (X .-> 1 +++ Y .-> 1)
test2 = distance (X .-> 1 +++ Y .-> 1 +++ origin)
test3 = distance (X .-> 1 +++ Y .-> 1 +++ Year .-> 2014)

move r dx dy = X := r!X + dx .| Y := r!Y + dy .| r
