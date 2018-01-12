-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Row.Records
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


module Data.Row.Records
  (
  -- * Types and constraints
    Label(..)
  , KnownSymbol, AllUniqueLabels, WellBehaved
  , Rec, Row, Empty
  -- * Construction
  , empty
  , type (.==), (.==), pattern (:==), unSingleton
  , defaultRecord, defaultRecordA
  , fromLabels, fromLabelsA
  -- ** Extension
  , extend, Extend, Lacks, type (.\)
  -- ** Restriction
  , type (.-), (.-)
  , restrict, split
  -- ** Modification
  , update, focus, Modify, rename, Rename
  -- * Query
  , HasType, type (.!), (.!)
  -- * Combine
  -- ** Disjoint union
  , type (.+), (.+), Disjoint, pattern (:+)
  -- * Row operations
  -- ** Map
  , Map, map, map'
  , transform, transform'
  -- ** Fold
  , Forall, erase, eraseWithLabels, eraseZip, eraseToHashMap
  -- ** Zip
  , Zip, zip
  -- ** Sequence
  , sequence
  -- ** Labels
  , labels
  -- ** UNSAFE operations
  , unsafeRemove, unsafeInjectFront
  )
where

import Prelude hiding (map, sequence, zip)

import Control.DeepSeq (NFData(..), deepseq)

import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Hashable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as M
import Data.List hiding (map, zip)
import qualified Data.List as L
import Data.Proxy
import Data.String (IsString)
import Data.Text (Text)

import GHC.TypeLits

import Unsafe.Coerce

import Data.Row.Internal


{--------------------------------------------------------------------
  Open records
--------------------------------------------------------------------}
-- | A record with row r.
data Rec (r :: Row *) where
  OR :: HashMap Text HideType -> Rec r

instance Forall r Show => Show (Rec r) where
  show r = "{ " ++ intercalate ", " binds ++ " }"
    where binds = (\ (x, y) -> x ++ "=" ++ y) <$> eraseWithLabels (Proxy @Show) show r

instance Forall r Eq => Eq (Rec r) where
  r == r' = and $ eraseZip (Proxy @Eq) (==) r r'

instance (Forall r Eq, Forall r Ord) => Ord (Rec r) where
  compare m m' = cmp $ eraseZip (Proxy @Ord) compare m m'
      where cmp l | [] <- l' = EQ
                  | a : _ <- l' = a
                  where l' = dropWhile (== EQ) l

instance (Forall r Bounded, AllUniqueLabels r) => Bounded (Rec r) where
  minBound = defaultRecord @Bounded minBound
  maxBound = defaultRecord @Bounded maxBound

instance Forall r NFData => NFData (Rec r) where
  rnf r = getConst $ metamorph @r @NFData @Rec @(Const ()) @Identity Proxy empty doUncons doCons r
    where empty = const $ Const ()
          doUncons l r = (Identity $ r .! l, unsafeRemove l r)
          doCons _ x r = deepseq x $ deepseq r $ Const ()

-- | The empty record
empty :: Rec Empty
empty = OR M.empty

-- | The singleton record
infix 7 .==
(.==) :: KnownSymbol l => Label l -> a -> Rec (l .== a)
l .== a = extend l a empty

infix 7 :==
pattern (:==) :: forall l a. KnownSymbol l => Label l -> a -> Rec (l .== a)
pattern l :== a <- (unSingleton @l @a -> (l, a)) where
        (:==) l a = l .== a

-- | Turns a singleton record into a pair of the label and value.
unSingleton :: forall l a. KnownSymbol l => Rec (l .== a) -> (Label l, a)
unSingleton r = (l, r .! l) where l = Label @l

{--------------------------------------------------------------------
  Basic record operations
--------------------------------------------------------------------}


-- | Record extension. The row may already contain the label,
--   in which case the origin value can be obtained after restriction ('.-') with
--   the label.
extend :: forall a l r. KnownSymbol l => Label l -> a -> Rec r -> Rec (Extend l a r)
extend (toKey -> l) a (OR m) = OR $ M.insert l (HideType a) m

-- | Update the value associated with the label.
update :: KnownSymbol l => Label l -> a -> Rec r -> Rec r
update (toKey -> l) a (OR m) = OR $ M.adjust f l m where f = const (HideType a)

-- | Focus on the value associated with the label.
focus :: (Functor f, KnownSymbol l) => Label l -> (r .! l -> f a) -> Rec r -> f (Rec (Modify l a r))
focus (toKey -> l) f (OR m) = case m M.! l of
  HideType x -> OR . flip (M.insert l) m . HideType <$> f (unsafeCoerce x)


-- | Rename a label.
rename :: (KnownSymbol l, KnownSymbol l') => Label l -> Label l' -> Rec r -> Rec (Rename l l' r)
rename (toKey -> l) (toKey -> l') (OR m) = OR $ M.insert l' (m M.! l) $ M.delete l m

-- | Record selection
(.!) :: KnownSymbol l => Rec r -> Label l -> r .! l
OR m .! (toKey -> a) = case m M.! a of
  HideType x -> unsafeCoerce x

infixl 8 .-
-- | Record restriction. Remove the label l from the record.
(.-) :: KnownSymbol l => Rec r -> Label l -> Rec (r .- l)
-- OR m .- _ = OR m
OR m .- (toKey -> a) = OR $ M.delete a m

-- | Record disjoint union (commutative)
infixl 6 .+
(.+) :: Rec l -> Rec r -> Rec (l .+ r)
OR l .+ OR r = OR $ M.unionWith (error "Impossible") l r


-- | A pattern version of record union, for use in pattern matching.
infixl 6 :+
pattern (:+) :: forall l r. Disjoint l r => Rec l -> Rec r -> Rec (l .+ r)
pattern l :+ r <- (split @l -> (l, r)) where
        (:+) l r = l .+ r

-- | Split a record into two sub-records.
split :: forall s r. (Forall s Unconstrained1, Subset s r)
         => Rec r -> (Rec s, Rec (r .\\ s))
split (OR m) = (OR $ M.intersection m labelMap, OR $ M.difference m labelMap)
  where labelMap = M.fromList $ L.zip (labels @s @Unconstrained1) (repeat ())

-- | Arbitrary record restriction.  Turn a record into a subset of itself.
restrict :: forall r r'. (Forall r Unconstrained1, Subset r r') => Rec r' -> Rec r
restrict = fst . split

-- | Removes a label from the record but does not remove the underlying value.
--
-- This is faster than regular record removal ('.-') but should only be used when
-- either: the record will never be merged with another record again, or a new
-- value will soon be placed into the record at this label (as in, an 'update'
-- that is split over two commands).
--
-- If the resulting record is then merged (with '.+') with another record that
-- contains a value at that label, an "Impossible" error will occur.
unsafeRemove :: KnownSymbol l => Label l -> Rec r -> Rec (r .- l)
unsafeRemove _ (OR m) = OR m


{--------------------------------------------------------------------
  Folds and maps
--------------------------------------------------------------------}
-- An easier type synonym for a pair where both elements are the same type.
type IPair = Product Identity Identity

-- Construct an IPair.
iPair :: τ -> τ -> IPair τ
iPair = (. Identity) . Pair . Identity

-- Destruct an IPair.  Easily used with ViewPatterns.
unIPair :: IPair τ -> (τ, τ)
unIPair (Pair (Identity x) (Identity y)) = (x,y)


-- | A standard fold
erase :: Forall r c => Proxy c -> (forall a. c a => a -> b) -> Rec r -> [b]
erase p f = fmap (snd @String) . eraseWithLabels p f

-- A fold with labels
eraseWithLabels :: forall s ρ c b. (Forall ρ c, IsString s) => Proxy c -> (forall a. c a => a -> b) -> Rec ρ -> [(s,b)]
eraseWithLabels _ f = getConst . metamorph @ρ @c @Rec @(Const [(s,b)]) @Identity Proxy doNil doUncons doCons
  where doNil _ = Const []
        doUncons l r = (Identity $ r .! l, unsafeRemove l r)
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => Label ℓ -> Identity τ -> Const [(s,b)] ('R ρ) -> Const [(s,b)] ('R (ℓ :-> τ ': ρ))
        doCons l (Identity x) (Const c) = Const $ (show' l, f x) : c

-- | A fold over two row type structures at once
eraseZip :: forall ρ c b. Forall ρ c => Proxy c -> (forall a. c a => a -> a -> b) -> Rec ρ -> Rec ρ -> [b]
eraseZip _ f x y = getConst $ metamorph @ρ @c @(Product Rec Rec) @(Const [b]) @IPair Proxy (const $ Const []) doUncons doCons (Pair x y)
  where doUncons l (Pair r1 r2) = (iPair a b, Pair r1' r2')
          where (a, r1') = (r1 .! l, unsafeRemove l r1)
                (b, r2') = (r2 .! l, unsafeRemove l r2)
        doCons :: forall ℓ τ ρ. c τ
               => Label ℓ -> IPair τ -> Const [b] ('R ρ) -> Const [b] ('R (ℓ :-> τ ': ρ))
        doCons _ (unIPair -> x) (Const c) = Const $ uncurry f x : c

-- | Turns a record into a 'HashMap' from values representing the labels to
--   the values of the record.
eraseToHashMap :: (IsString s, Eq s, Hashable s, Forall r c) =>
                  Proxy c -> (forall a . c a => a -> b) -> Rec r -> HashMap s b
eraseToHashMap p f r = M.fromList $ eraseWithLabels p f r

-- | RMap is used internally as a type level lambda for defining record maps.
newtype RMap (f :: * -> *) (ρ :: Row *) = RMap { unRMap :: Rec (Map f ρ) }

-- | A function to map over a record given a constraint.
map :: forall c f r. Forall r c => (forall a. c a => a -> f a) -> Rec r -> Rec (Map f r)
map f = unRMap . metamorph @r @c @Rec @(RMap f) @Identity Proxy doNil doUncons doCons
  where
    doNil _ = RMap empty
    doUncons l r = (Identity $ r .! l, unsafeRemove l r)
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> Identity τ -> RMap f ('R ρ) -> RMap f ('R (ℓ :-> τ ': ρ))
    doCons l (Identity v) (RMap r) = RMap (unsafeInjectFront l (f v) r)

-- | A function to map over a record given no constraint.
map' :: forall f r. Forall r Unconstrained1 => (forall a. a -> f a) -> Rec r -> Rec (Map f r)
map' = map @Unconstrained1

-- | Lifts a natrual transformation over a record.  In other words, it acts as a
-- record transformer to convert a record of @f a@ values to a record of @g a@
-- values.  If no constraint is needed, instantiate the first type argument with
-- 'Unconstrained1'.
transform :: forall c r f g. Forall r c => (forall a. c a => f a -> g a) -> Rec (Map f r) -> Rec (Map g r)
transform f = unRMap . metamorph @r @c @(RMap f) @(RMap g) @f Proxy doNil doUncons doCons . RMap
  where
    doNil _ = RMap empty
    doUncons l (RMap r) = (r .! l, RMap $ unsafeRemove l r)
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
           => Label ℓ -> f τ -> RMap g ('R ρ) -> RMap g ('R (ℓ :-> τ ': ρ))
    doCons l v (RMap r) = RMap (unsafeInjectFront l (f v) r)

transform' :: forall r f g. Forall r Unconstrained1 => (forall a. f a -> g a) -> Rec (Map f r) -> Rec (Map g r)
transform' = transform @Unconstrained1 @r

-- | Applicative sequencing over a record
sequence :: forall f r. (Forall r Unconstrained1, Applicative f) => Rec (Map f r) -> f (Rec r)
sequence = getCompose . metamorph @r @Unconstrained1 @(RMap f) @(Compose f Rec) @f Proxy doNil doUncons doCons . RMap
  where
    doNil _ = Compose (pure empty)
    doUncons l (RMap r) = (r .! l, RMap $ unsafeRemove l r)
    doCons l fv (Compose fr) = Compose $ unsafeInjectFront l <$> fv <*> fr

-- | RZipPair is used internally as a type level lambda for zipping records.
newtype RZipPair (ρ1 :: Row *) (ρ2 :: Row *) = RZipPair { unRZipPair :: Rec (Zip ρ1 ρ2) }

-- | Zips together two records that have the same set of labels.
zip :: forall r1 r2. Forall2 r1 r2 Unconstrained1 => Rec r1 -> Rec r2 -> Rec (Zip r1 r2)
zip r1 r2 = unRZipPair $ metamorph2 @r1 @r2 @Unconstrained1 @Rec @Rec @RZipPair @Identity @Identity Proxy Proxy doNil doUncons doCons r1 r2
  where
    doNil _ _ = RZipPair empty
    doUncons l r1 r2 = ((Identity $ r1 .! l, unsafeRemove l r1), (Identity $ r2 .! l, unsafeRemove l r2))
    doCons l (Identity v1) (Identity v2) (RZipPair r) = RZipPair $ unsafeInjectFront l (v1, v2) r

-- | A helper function for unsafely adding an element to the front of a record
-- This can cause the resulting record to be malformed, for instance, if the record
-- already contains labels that are "less than" the given label.
-- Realistically, this function should only be used when writing calls to 'metamorph'.
unsafeInjectFront :: KnownSymbol l => Label l -> a -> Rec (R r) -> Rec (R (l :-> a ': r))
unsafeInjectFront (toKey -> a) b (OR m) = OR $ M.insert a (HideType b) m


{--------------------------------------------------------------------
  Record initialization
--------------------------------------------------------------------}

-- | Initialize a record with a default value at each label.
defaultRecord :: forall c ρ. (Forall ρ c, AllUniqueLabels ρ) => (forall a. c a => a) -> Rec ρ
defaultRecord v = runIdentity $ defaultRecordA @c $ pure v

-- | Initialize a record with a default value at each label; works over an 'Applicative'.
defaultRecordA :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
               => (forall a. c a => f a) -> f (Rec ρ)
defaultRecordA v = fromLabelsA @c $ pure v

-- | Initialize a record, where each value is determined by the given function over
-- the label at that value.
fromLabels :: forall c ρ. (Forall ρ c, AllUniqueLabels ρ)
           => (forall l a. (KnownSymbol l, c a) => Label l -> a) -> Rec ρ
fromLabels f = runIdentity $ fromLabelsA @c $ (pure .) f

-- | Initialize a record, where each value is determined by the given function over
-- the label at that value.  This function works over an 'Applicative'.
fromLabelsA :: forall c f ρ. (Applicative f, Forall ρ c, AllUniqueLabels ρ)
            => (forall l a. (KnownSymbol l, c a) => Label l -> f a) -> f (Rec ρ)
fromLabelsA mk = getCompose $ metamorph @ρ @c @(Const ()) @(Compose f Rec) @(Const ()) Proxy doNil doUncons doCons (Const ())
  where doNil _ = Compose $ pure empty
        doUncons _ _ = (Const (), Const ())
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c τ)
               => Label ℓ -> Const () τ -> Compose f Rec ('R ρ) -> Compose f Rec ('R (ℓ :-> τ ': ρ))
        doCons l _ (Compose r) = Compose $ unsafeInjectFront l <$> mk l <*> r

