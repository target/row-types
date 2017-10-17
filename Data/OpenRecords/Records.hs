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
             KnownSymbol,
             Rec,   Row,
             -- * Construction
             empty, Empty,
             rinit, rinitA, rinitAWithLabel,
             -- ** Extension
             Extendable(..), Extend,
             -- ** Renaming
             Renamable(..), Rename,
             -- ** Restriction
             (.-), (:-),
             Restrict(..),
             -- ** Update
             Updatable(..),
             -- * Query
             (.!), (:!),
             -- * Focus
             Focusable(..), Modify,
             -- * Combine
             -- ** Union
              (.++), (:++),
             -- ** Disjoint union
              (.+) , (:+),
             -- * Row constraints
             (:\), Disjoint, Labels, Forall(..), Erasable(..),
             RowMap(..), RowMapC(..), RowMapCF(..), RowZip(..),
             eraseToHashMap,
             -- * Row only operations
             -- * Syntactic sugar
             RecOp(..), RowOp(..), (.|), (:|),
             -- * Labels
             labels

     )
where

import Control.Monad.Identity

import Data.Functor.Const
import Data.Hashable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as M
import Data.List
import Data.Proxy
import Data.Sequence (Seq,ViewL(..),(><),(<|))
import qualified Data.Sequence as S
import Data.String (IsString)

import GHC.TypeLits
import GHC.Exts -- needed for constraints kinds

import Unsafe.Coerce

import Data.OpenRecords.Internal.Row





{--------------------------------------------------------------------
  Open records
--------------------------------------------------------------------}
-- | A record with row r.
data Rec (r :: Row *) where
  OR :: HashMap String (Seq HideType) -> Rec r

instance (Forall r Show) => Show (Rec r) where
  show r = "{ " ++ intercalate ", " binds ++ " }"
    where binds = (\ (x, y) -> x ++ "=" ++ y) <$> eraseWithLabels (Proxy @Show) show r

instance (Forall r Eq) => Eq (Rec r) where
  r == r' = and $ eraseZip (Proxy @Eq) (==) r r'

instance (Eq (Rec r), Forall r Ord) => Ord (Rec r) where
  compare m m' = cmp $ eraseZip (Proxy @Ord) compare m m'
      where cmp l | [] <- l' = EQ
                  | a : _ <- l' = a
                  where l' = dropWhile (== EQ) l

instance (Forall r Bounded) => Bounded (Rec r) where
  minBound = rinit (Proxy @Bounded) minBound
  maxBound = rinit (Proxy @Bounded) maxBound

type instance ValOf Rec τ = τ

-- | The empty record
empty :: Rec Empty
empty = OR M.empty

{--------------------------------------------------------------------
  Basic record operations
--------------------------------------------------------------------}


instance Extendable Rec where
  type Inp Rec a = a
  -- | Record extension. The row may already contain the label,
  --   in which case the origin value can be obtained after restriction ('.-') with
  --   the label.
  extend (show -> l) a (OR m) = OR $ M.insert l v m
     where v = HideType a <| M.lookupDefault S.empty l m


instance Updatable Rec where
  -- | Update the value associated with the label.
  update (show -> l) a (OR m) = OR $ M.adjust f l m where f = S.update 0 (HideType a)


instance Focusable Rec where
  -- | Focus on the value associated with the label.
  focus (show -> l) f (OR m) = case S.viewl (m M.! l) of
    HideType x :< v -> OR . flip (M.insert l) m . (<| v) . HideType <$> f (unsafeCoerce x)
    EmptyL -> error "Impossible Record state when focusing"


instance Renamable Rec where
  -- | Rename a label. The row may already contain the new label,
  --   in which case the origin value can be obtained after restriction ('.-') with
  --   the new label.
  rename l l' r = extend l' (r .! l) (r .- l)

-- | Record selection
(.!) :: KnownSymbol l => Rec r -> Label l -> r :! l
OR m .! (show -> a) = x'
   where x S.:< _ =  S.viewl $ m M.! a
         -- notice that this is safe because of the external type
         x' = case x of HideType p -> unsafeCoerce p



infix  8 .-
-- | Record restriction. Delete the label l from the record.
(.-) :: KnownSymbol l =>  Rec r -> Label l -> Rec (r :- l)
OR m .- (show -> a) = OR m'
   where _ S.:< t =  S.viewl $ m M.! a
         m' = case S.viewl t of
               EmptyL -> M.delete a m
               _      -> M.insert a t m



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

{--------------------------------------------------------------------
  Folds and maps
--------------------------------------------------------------------}
instance Erasable Rec where
  type Output Rec a = [a]
  type OutputZip Rec a = [a]
  erase p f = fmap (snd @String) . eraseWithLabels p f
  eraseWithLabels :: forall s ρ c b. (Forall ρ c, IsString s) => Proxy c -> (forall a. c a => a -> b) -> Rec ρ -> [(s,b)]
  eraseWithLabels _ f = getConst . metamorph @ρ @c @Rec @(Const [(s,b)]) doNil doUncons doCons
    where doNil _ = Const []
          doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                   => Rec ('R (ℓ :-> τ ': ρ)) -> (τ, Rec ('R ρ))
          doUncons r = (r .! l, r .- l) where l = Label @ℓ
          doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => τ -> Const [(s,b)] ('R ρ) -> Const [(s,b)] ('R (ℓ :-> τ ': ρ))
          doCons x (Const c) = Const $ (show' (Label @ℓ), f x) : c
  eraseZip :: forall ρ c b. Forall ρ c => Proxy c -> (forall a. c a => a -> a -> b) -> Rec ρ -> Rec ρ -> [b]
  eraseZip _ f x y = getConst $ metamorph @ρ @c @(RowPair Rec) @(Const [b]) (const $ Const []) doUncons doCons (RowPair (x,y))
    where doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                   => (RowPair Rec) ('R (ℓ :-> τ ': ρ)) -> ((τ,τ), (RowPair Rec) ('R ρ))
          doUncons (RowPair (r1, r2)) = ((r1 .! l, r2 .! l), RowPair (r1 .- l, r2 .- l)) where l = Label @ℓ
          doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => (τ,τ) -> Const [b] ('R ρ) -> Const [b] ('R (ℓ :-> τ ': ρ))
          doCons x (Const c) = Const $ uncurry f x : c

-- | Turns a record into a 'HashMap' from values representing the labels to
--   the values of the record.
eraseToHashMap :: (IsString s, Eq s, Hashable s, Forall r c) =>
                  Proxy c -> (forall a . c a => a -> b) -> Rec r -> HashMap s b
eraseToHashMap p f r = M.fromList $ eraseWithLabels p f r


-- | A class for mapping a function over a record.
-- TODO: Can this be made more generic?
class RowMap (f :: * -> *) (r :: Row *) where
  type Map f r :: Row *
  rmap :: Proxy f -> (forall a.  a -> f a) -> Rec r -> Rec (Map f r)
  rsequence :: Applicative f => Proxy f -> Rec (Map f r) -> f (Rec r)

instance RowMapx f r => RowMap f (R r) where
  type Map f (R r) = R (RM f r)
  rmap = rmap'
  rsequence = rsequence'

-- | A helper class for mapping a function over a record.
-- TODO: Can this be made more generic?
class RowMapx (f :: * -> *) (r :: [LT *]) where
  type RM f r :: [LT *]
  rmap' :: Proxy f -> (forall a.  a -> f a) -> Rec (R r) -> Rec (R (RM f r))
  rsequence' :: Applicative f => Proxy f -> Rec (R (RM f r)) -> f (Rec (R r))

instance RowMapx f '[] where
  type RM f '[] = '[]
  rmap' _ _ _ = empty
  rsequence' _ _ = pure empty

instance (KnownSymbol l,  RowMapx f t) => RowMapx f (l :-> v ': t) where
  type RM f (l :-> v ': t) = l :-> f v ': RM f t
  rmap' w f r = unsafeInjectFront l (f (r .! l)) (rmap' w f (r .- l))
    where l = Label :: Label l
  rsequence' w r = unsafeInjectFront l <$> r .! l <*> rsequence' w (r .- l)
    where l = Label :: Label l


-- | A class for mapping a function over a record where each element of the record
-- satisfies a constraint.
-- TODO: Can this be made more generic?
class RowMapCF (c :: * -> Constraint) (f :: * -> *) (r :: Row *) where
  type MapCF c f r :: Row *
  rmapcf :: Proxy c -> Proxy f -> (forall a. c a => a -> f a) -> Rec r -> Rec (MapCF c f r)

instance RMapcf c f r => RowMapCF c f (R r) where
  type MapCF c f (R r) = R (RMappf c f r)
  rmapcf = rmapcf'

-- | A helper class for mapping a function over a record where each element of the record
-- satisfies a constraint.
-- TODO: Can this be made more generic?
class RMapcf (c :: * -> Constraint) (f :: * -> *) (r :: [LT *]) where
  type RMappf c f r :: [LT *]
  rmapcf' :: Proxy c -> Proxy f -> (forall a. c a => a -> f a) -> Rec (R r) -> Rec (R (RMappf c f r))

instance RMapcf c f '[] where
  type RMappf c f '[] = '[]
  rmapcf' _ _ _ _ = empty

instance (KnownSymbol l, c v, RMapcf c f t) => RMapcf c f (l :-> v ': t) where
  type RMappf c f (l :-> v ': t) = l :-> f v ': RMappf c f t
  rmapcf' c w f r = unsafeInjectFront l (f (r .! l)) (rmapcf' c w f (r .- l))
    where l = Label :: Label l


-- | A class for mapping a function over a record where each element of the record
-- satisfies a constraint and the types don't change.
-- TODO: Can this be made more generic?
class RowMapC (c :: * -> Constraint) (r :: Row *) where
  type MapC c r :: Row *
  rmapc :: Proxy c -> (forall a. c a => a -> a) -> Rec r -> Rec (MapC c r)

instance RMapc c r => RowMapC c (R r) where
  type MapC c (R r) = R (RMapp c r)
  rmapc = rmapc'

-- | A class for mapping a function over a record where each element of the record
-- satisfies a constraint and the types don't change.
-- TODO: Can this be made more generic?
class RMapc (c :: * -> Constraint) (r :: [LT *]) where
  type RMapp c r :: [LT *]
  rmapc' :: Proxy c -> (forall a. c a => a -> a) -> Rec (R r) -> Rec (R (RMapp c r))

instance RMapc c '[] where
  type RMapp c '[] = '[]
  rmapc' _ _ _ = empty

instance (KnownSymbol l, c v, RMapc c t) => RMapc c (l :-> v ': t) where
  type RMapp c (l :-> v ': t) = l :-> v ': RMapp c t
  rmapc' c f r = unsafeInjectFront l (f (r .! l)) (rmapc' c f (r .- l))
    where l = Label :: Label l


-- | A class for zipping two records together.
-- TODO: Can this be made more generic?
class RowZip (r1 :: Row *) (r2 :: Row *) where
  type RZip r1 r2 :: Row *
  rzip :: Rec r1 -> Rec r2 -> Rec (RZip r1 r2)

instance RZipt r1 r2 => RowZip (R r1) (R r2) where
  type RZip (R r1) (R r2) = R (RZipp r1 r2)
  rzip = rzip'

-- | A helper class for zipping two records together.
-- TODO: Can this be made more generic?
class RZipt (r1 :: [LT *]) (r2 :: [LT *]) where
  type RZipp r1 r2 :: [LT *]
  rzip' :: Rec (R r1) -> Rec (R r2) -> Rec (R (RZipp r1 r2))

instance RZipt '[] '[] where
  type RZipp '[] '[] = '[]
  rzip' _ _ = empty

instance (KnownSymbol l, RZipt t1 t2) =>
   RZipt (l :-> v1 ': t1) (l :-> v2 ': t2) where

   type RZipp (l :-> v1 ': t1) (l :-> v2 ': t2) = l :-> (v1,v2) ': RZipp t1 t2
   rzip' r1 r2 = unsafeInjectFront l (r1 .! l, r2 .! l) (rzip' (r1 .- l) (r2 .- l))
       where l = Label :: Label l

-- | A helper function for unsafely adding an element to the front of a record
unsafeInjectFront :: KnownSymbol l => Label l -> a -> Rec (R r) -> Rec (R (l :-> a ': r))
unsafeInjectFront (show -> a) b (OR m) = OR $ M.insert a v m
  where v = HideType b <| M.lookupDefault S.empty a m


{--------------------------------------------------------------------
  Record initialization
--------------------------------------------------------------------}
newtype FRow (f :: * -> *) (ρ :: Row *) = FRow { unFRow :: f (Rec ρ) }

-- | Initialize a record, where each value is determined by the given function over
-- the label at that value.  This function works over an 'Applicative'.
rinitAWithLabel :: forall f ρ c. (Applicative f, Forall ρ c)
                => Proxy c -> (forall l a. (KnownSymbol l, c a) => Label l -> f a) -> f (Rec ρ)
rinitAWithLabel _ mk = unFRow $ metamorph @ρ @c @(Const ()) @(FRow f) doNil doUncons doCons (Const ())
  where doNil :: Const () Empty -> FRow f Empty
        doNil _ = FRow $ pure empty
        doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
                 => Const () ('R (ℓ :-> τ ': ρ)) -> ((), Const () ('R ρ))
        doUncons _ = ((), Const ())
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => () -> FRow f ('R ρ) -> FRow f ('R (ℓ :-> τ ': ρ))
        doCons _ (FRow r) = FRow $ unsafeInjectFront (Label @ℓ) <$> mk @ℓ @τ (Label @ℓ) <*> r

-- | Initialize a record with a default value at each label; works over an 'Applicative'.
rinitA :: forall f ρ c. (Applicative f, Forall ρ c)
       => Proxy c -> (forall a. c a => f a) -> f (Rec ρ)
rinitA p f = rinitAWithLabel p (pure f)

-- | Initialize a record with a default value at each label.
rinit :: Forall r c => Proxy c -> (forall a. c a => a) -> Rec r
rinit p mk = runIdentity $ rinitA p $ pure mk


