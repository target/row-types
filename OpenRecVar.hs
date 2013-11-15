{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds, RankNTypes, DataKinds #-}
{-# LANGUAGE FunctionalDependencies, IncoherentInstances, MultiParamTypeClasses,UndecidableInstances,FlexibleInstances,ViewPatterns,ScopedTypeVariables,OverlappingInstances #-} 

module OpenRecVar(Label,To(..), TList(..),GetType,Remove,Conc, 
                  OpenVar,inj,decomp, 
                  OpenRec, empty, (.->), (+++), (!), (.-), rename, (:>)(..), (.|)
                  ) 
where

import Data.Typeable
import Data.Map(Map,unionWith)
import Data.Sequence(Seq,viewl,ViewL(..),(><),(<|))
import qualified Data.Map as M
import qualified Data.Sequence as S
import Data.Foldable
import Unsafe.Coerce
import Data.List
import GHC.Exts

class Empty a
instance Empty a

class (Typeable l, Show l) => Label l

infixr 6 :-> 
data To l t = l :-> t
infixr 5 :::
data TList a = a ::: TList a | N

class GetType (l :: *) (m :: TList (To * *)) (t :: *) | l m -> t
instance GetType l (l :-> t ::: r) t
instance GetType l x t => GetType l (l' :-> t' ::: x) t
instance 


class Remove (l :: *) (m :: TList (To * *)) (m' :: TList (To * *)) | l m -> m'
instance Remove l (l :-> t ::: r) r
instance Remove l x y => Remove l (l' :-> t' ::: x) (l' :-> t' ::: y)

class Conc (l :: TList (To * *)) (r :: TList (To * *)) (z :: TList (To * *)) | l r -> z
instance Conc N r r
instance Conc l r z => Conc (x :-> t ::: l) r (x :-> t ::: z)


data OpenVar (m :: TList (To * *))  where
  OV :: Label l => l -> t -> OpenVar m -- Constructor not exported

inj :: (Label l, GetType l m t) => l -> t -> OpenVar m
inj = OV

data Constrained (c :: * -> Constraint) where
  Constrained :: c a => a -> Constrained c



decomp :: forall l t c m m'. (Label l, GetType l m t, Remove l m m') => 
              l -> OpenVar m -> Either (OpenVar m') t
decomp _ (OV l t) = case (cast l :: Maybe l) of
   Just _ -> Right $ unsafeCoerce t
   Nothing -> Left $ OV l t



data HideType where
  HideType :: Label l => l -> a -> HideType


data OpenRec (m :: TList (To * *)) = 
  OR (Map TypeRep (Seq HideType)) -- Constructor not exported


empty :: OpenRec N 
empty = OR M.empty

infixr 6 .->
(.->) :: Label l => l -> t -> OpenRec (l :-> t ::: N)
l .-> t = OR (M.singleton (typeOf l) (S.singleton (HideType l t)))

infixr 5 +++
(+++) :: Conc l r z => OpenRec l -> OpenRec r -> OpenRec z
(OR l) +++ (OR r) = OR $ unionWith (><) l r

infixl 9 !
(!) :: (Label l, GetType l m t) => OpenRec  m -> l ->  t
(OR m) ! l = 
    case viewl $ m M.! typeOf l of
      HideType _ a :< _ -> unsafeCoerce a

infixl 6 .-
(.-) :: (Label l, Remove l m m') => OpenRec m -> l -> OpenRec  m'
(OR m) .- l' = OR $ 
    case viewl (seqTail (m M.! l)) of
       EmptyL   -> M.delete l m
       h :< t   -> M.insert l (h <| t) m        
  where seqTail (viewl -> _ :< t) = t
        l = typeOf l'

data l :> t = l := t

infixr 5 :=

infixr 4 .|
(.|) :: (Label l, GetType l m t) => l :> t -> OpenRec m -> OpenRec m
(l := t) .| (OR m) = OR (M.adjust up (typeOf l) m) where
   up (viewl -> _ :< x) = HideType l t <| x



rename l l' m = l' .-> m ! l +++ m .- l




{-

-- this is better when closed type families are in GHC release

type TMap a b = TList (a :-> b)

type family GetType (l :: *) (m :: TList (To * *)) :: (t :: *) where
  GetType l (l :-> t ::: r) = t
  GetType l (l' :-> t' ::: x) t = GetType l x 

type family Remove (l :: Label)  (m :: TMap * *) :: TMap * * where
  Remove l  (l :-> t ::: r) = r
  Remove l  (l' :-> t' ::: r) = l' :-> t' ::: Remove l r

type family  Conc (l :: TList (To * *)) (r :: TList (To * *)) :: TList (To * *) where
   Conc N r = r
   Conc (x :-> t ::: l) r = x :-> t ::: Conc l r
-}
