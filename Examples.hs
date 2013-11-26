{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds, RankNTypes, DataKinds #-}
{-# LANGUAGE DeriveDataTypeable,TypeFamilies, ViewPatterns, DataKinds, ConstraintKinds #-}
module Examples where
import Prelude hiding ((.))
import OpenRecVar

-- Examples from the paper "Extensible records with scoped labels" by Daan Leijen

-- this is just for readability...
infix 9 .
(.) ::  KnownSymbol a => OpenRec m -> Label a -> Get a m
(.) = (!)

x = Label :: Label "x"
y = Label :: Label "y"

origin = x := 0 .| y := 0 .| empty

-- diferent order, same result!
origin2 = y := 0 .| x := 0 .| empty

z = Label :: Label "z"

origin3 = z := 0 .| origin

name = Label :: Label "name"

named s r = name := s .| r

distance p = sqrt $ p.x * p.x + p.y * p.y

test1 = distance (named "2d" origin) + distance origin3

move p dx dy = update x (p.x + dx) $
               update y (p.y + dy) p

--typerr1 = (x := 1 .| empty) . y
--typerr2 = distance (x := 1 .| empty)

freeext = x := 1 .| origin

selfst = (x := 2 .| x := True .| empty) . x
selsnd = ((x := 2 .| x := True .| empty) .- x) . x





