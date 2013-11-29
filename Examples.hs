
{-# LANGUAGE TypeOperators,KindSignatures,TypeFamilies, DataKinds, AllowAmbiguousTypes #-}
module Examples where
import Prelude hiding ((.))
import OpenRecVar

-- Examples from the paper "Extensible records with scoped labels" by Daan Leijen

-- notice Extensible records implement Show Eq and Ord and such, given that all element have 
-- the corresponding type class

-- this is just for readability...
infix 9 .
(.) ::  KnownSymbol l => Rec r -> Label l -> r :! l
(.) = (.!)

-- it would be nice to write 'x instead of going to the trouble to declare this label
x = Label :: Label "x"
y = Label :: Label "y"
z = Label :: Label "z"
name = Label :: Label "name"

-- inferred type (cannot be written down because OpenRecVar.R is not exported):  origin :: Rec ('OpenRecVar.R '["x" ':= Integer, "y" ':= Integer])
-- nice type:
origin :: Rec ("x" := Integer :| "y" := Integer :| Empty)
origin = x := 0 .| y := 0 .| empty
-- { x=0.0, y=0.0 }

-- diferent order, same result!
-- Inferred type: origin2 :: Rec ('OpenRecVar.R '["x" ':= Integer, "y" ':= Integer])
origin2 = y := 0 .| x := 0 .| empty
-- { x=0.0, y=0.0 }

test = origin == origin2
-- True

origin3 = z := 0 .| origin
-- { x=0.0, y=0.0, z=0 }

-- type is inferred!
named ::  a -> Rec r -> Rec ("name" := a :| r)
named s r = name := s .| r
{-
-- inferred type:
-- distance
--  :: (Floating t, Get "y" m ~ t, Get "x" m ~ t) =>
--     OpenRec m -> Get "x" m

distance p = sqrt $ p.x * p.x + p.y * p.y

test1 = distance (named "2d" origin) + distance origin3
-- 0.0

-- inferred type:
-- move :: (Num t1, Num t, Get "y" m ~ t1, Get "x" m ~ t) =>
--     OpenRec m -> Get "x" m -> Get "y" m -> OpenRec m

move p dx dy = update x (p.x + dx) $
               update y (p.y + dy) p

test2 = move (named "foo" origin3) 10 10
-- { name="foo", x=10.0, y=10.0, z=0 }


-- some type errors
--typerr1 = (x := 1 .| empty) . y
--typerr2 = distance (x := 1 .| empty)

freeext = x := 1 .| origin

selfst = (x := 2 .| x := True .| empty) . x
-- 2
selsnd = ((x := 2 .| x := True .| empty) .- x) . x
-- True
-}
{-
-- variant tests
testadam =  case inj x (1 :: Double) of
    v | Right a <- decomp x v -> a :: Double
    -- _ -> 5 -- aside: any guarantees about this being unreachable?
-}



