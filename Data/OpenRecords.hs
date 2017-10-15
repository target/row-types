-----------------------------------------------------------------------------
-- |
-- Module      :  Data.OpenRecords
-- Copyright   :  (c) Atze van der Ploeg 2013
-- License     :  BSD-style
-- Maintainer  :  atzeus@gmail.org
-- Stability   :  expirimental
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


module Data.OpenRecords
  (
    module Data.OpenRecords.Records
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

import Data.OpenRecords.Records


