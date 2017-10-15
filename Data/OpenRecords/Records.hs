-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords.Records
--
-- This module implements extensible records using closed type famillies.
--
-- See Examples.hs for examples.
--
-- Lists of (label,type) pairs are kept sorted thereby ensuring
-- that { x = 0, y = 0 } and { y = 0, x = 0 } have the same type.
--
-- In this way we can implement standard type classes such as Show, Eq, Ord and Bounded
-- for open records, given that all the elements of the open record satify the constraint.
--
-----------------------------------------------------------------------------


module Data.OpenRecords.Records

 (
             -- * Types and constraints
             Label(..),
             KnownSymbol(..),
             Rec,   Row,
             -- * Construction
             empty,Empty ,
             -- ** Extension
             extend, extendUnique, Extend,
             -- ** Renaming
             rename, renameUnique, Rename,
             -- ** Restriction
             (.-), (:-),
             Restrict(..),
             -- ** Update
             update,
             -- * Query
             (.!), (:!),
             -- * Focus
             focus, Modify,
             -- * Combine
             -- ** Union
              (.++), (:++),
             -- ** Disjoint union
              (.+) , (:+),
             -- * Row constraints
             (:\), Disjoint, Labels, Forall(..),
             RowMap(..), RowMapC(..), RowMapCF(..),
             -- * Row only operations
             -- * Syntactic sugar
             RecOp(..), RowOp(..), (.|), (:|),
             -- * Labels
             labels

     )
where

import Data.Functor.Const
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import Data.Sequence(Seq,viewl,ViewL(..),(><),(<|))
import qualified Data.HashMap.Lazy as M
import qualified Data.Sequence as S
import Unsafe.Coerce
import Data.List
import Data.Maybe (fromMaybe)
import Data.String (IsString (fromString))
import GHC.TypeLits
import GHC.Exts -- needed for constraints kinds
import Data.Proxy
import Data.Type.Equality (type (==))
import Unconstrained

import Data.OpenRecords.Internal.Row





{--------------------------------------------------------------------
  Open records
--------------------------------------------------------------------}

-- | The empty record
-- empty :: Rec Empty
-- empty = OR M.empty

{--------------------------------------------------------------------
  Basic record operations
--------------------------------------------------------------------}


-- | Record extension. The row may already contain the label,
--   in which case the origin value can be obtained after restriction ('.-') with
--   the label.
-- extend :: KnownSymbol l => Label l -> a -> Rec r -> Rec (Extend l a r)
-- extend (show -> l) a (OR m) = OR $ M.insert l v m
--    where v = HideType a <| M.lookupDefault S.empty l m

-- | Record extension without shadowing. The row may not already contain label l.
-- extendUnique :: (KnownSymbol l,r :\ l) => Label l -> a -> Rec r -> Rec (Extend l a r)
-- extendUnique = extend

-- | Update the value associated with the label.
-- update :: KnownSymbol l => Label l -> r :! l -> Rec r -> Rec r
-- update (show -> l) a (OR m) = OR $ M.adjust f l m where f = S.update 0 (HideType a)

-- | Focus on the value associated with the label.
-- focus :: (Functor f, KnownSymbol l) => Label l -> (r :! l -> f a) -> Rec r -> f (Rec (Modify l a r))
-- focus (show -> l) f r@(OR m) = case S.viewl (m M.! l) of HideType x :< v -> OR . flip (M.insert l) m . (<| v) . HideType <$> f (unsafeCoerce x)

-- | Rename a label. The row may already contain the new label ,
--   in which case the origin value can be obtained after restriction ('.-') with
--   the new label.
-- rename :: (KnownSymbol l, KnownSymbol l') => Label l -> Label l' -> Rec r -> Rec (Rename l l' r)
-- rename l l' r = extend l' (r .! l) (r .- l)

-- | Rename a label. The row may not already contain the new label.
-- renameUnique :: (KnownSymbol l, KnownSymbol l', r :\ l') => Label l -> Label l' -> Rec r -> Rec (Rename l l' r)
-- renameUnique = rename

-- -- | Record selection
-- (.!) :: KnownSymbol l => Rec r -> Label l -> r :! l
-- OR m .! (show -> a) = x'
--    where x S.:< t =  S.viewl $ m M.! a
--          -- notice that this is safe because of the external type
--          x' = case x of HideType p -> unsafeCoerce p
--
--
--
-- infix  8 .-
-- -- | Record restriction. Delete the label l from the record.
-- (.-) :: KnownSymbol l =>  Rec r -> Label l -> Rec (r :- l)
-- OR m .- (show -> a) = OR m'
--    where x S.:< t =  S.viewl $ m M.! a
--          m' = case S.viewl t of
--                EmptyL -> M.delete a m
--                _      -> M.insert a t m



-- | Record union (not commutative)
(.++) :: Rec l -> Rec r -> Rec (l :++ r)
OR l .++ OR r = OR $ M.unionWith (><) l r

-- | Record disjoint union (commutative)
(.+) :: Disjoint l r => Rec l -> Rec r -> Rec (l :+ r)
OR l .+ OR r = OR $ M.unionWith (error "Impossible") l r

-- | A class for restricting a Record to a particular set of labels
class Restrict (ls :: [Symbol]) where
  type Restricted ls (r :: Row *) :: Row *
  restrict :: Rec r -> Rec (Restricted ls r)

instance Restrict '[] where
  type Restricted '[] r = Empty
  restrict _ = empty

instance (KnownSymbol l, Restrict ls) => Restrict (l ': ls) where
  type Restricted (l ': ls) r = Extend l (r :! l) (Restricted ls r)
  restrict r = extend (Label @l) (r .! Label @l) (restrict @ls r)

{--------------------------------------------------------------------
  Syntactic sugar for record operations
--------------------------------------------------------------------}
-- | Here we provide a datatype for denoting record operations. Use '.|' to
--   actually apply the operations.
--
--   This allows us to chain operations with nicer syntax.
--   For example we can write:
--
-- > p :<-| z .| y :<- 'b' .| z :!= False .| x := 2 .| y := 'a' .| empty
--
-- Which results in:
--
-- > { p=False, x=2, y='b' }
--
-- Without this sugar, we would have written it like this:
--
-- >  rename z p $ update y 'b' $ extendUnique z False $ extend x 2 $ extend y 'a' empty
--
--
--  [@:<-@] Record update. Sugar for 'update'.
--
--  [@:=@] Record extension. Sugar for 'extend'.
--
--  [@:!=@] Record extension, without shadowing. Sugar for 'extendUnique'.
--
--  [@:<-|@] Record label renaming. Sugar for 'rename'.
--
--  [@:<-!@] Record label renaming. Sugar for 'renameUnique'.
infix 5 :=
infix 5 :!=
infix 5 :<-
data RecOp (c :: Row * -> Constraint) (rowOp :: RowOp *) where
  (:<-)  :: KnownSymbol l           => Label l -> a      -> RecOp (HasType l a) RUp
  (:=)   :: KnownSymbol l           => Label l -> a      -> RecOp Unconstrained1 (l ::= a)
  (:!=)  :: KnownSymbol l => Label l -> a      -> RecOp (Lacks l) (l ::= a)
  (:<-|) :: (KnownSymbol l, KnownSymbol l') => Label l' -> Label l -> RecOp Unconstrained1 (l' ::<-| l)
  (:<-!) :: (KnownSymbol l, KnownSymbol l', r :\ l') => Label l' -> Label l -> RecOp (Lacks l') (l' ::<-| l)




-- | Apply an operation to a record.
infixr 4 .|
(.|) :: c r => RecOp c ro -> Rec r -> Rec (ro :| r)
(l :<- a)   .| m  = update l a m
(l := a)    .| m  = extend l a m
(l :!= a)   .| m  = extendUnique l a m
(l' :<-| l) .| m  = rename l l' m
(l' :<-! l) .| m  = renameUnique l l' m

