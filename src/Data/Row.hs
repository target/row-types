{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Row
--
-- This module includes a set of common functions for Records and Variants.
-- It includes:
--
-- * Common constructors, destructors, and querying functions
--
-- It specifically excludes:
--
-- * Functions that have the same name for Records and Variants (e.g. 'focus',
--   'update', 'fromLabels', etc.)
--
-- * Common clashes with the standard Prelude or other modules (e.g. 'map',
--   'sequence', 'zip', 'Map', etc.)
--
-- If these particular functions are needed, they should be brought in qualified
-- from one of the Data.Row.*** modules directly.
--
-----------------------------------------------------------------------------


module Data.Row
  (
  -- * Types and constraints
    Label(..)
  , KnownSymbol, AllUniqueLabels, WellBehaved
  , Var, Rec, Row, Empty, type (≈)
  , HasType, Subset, Lacks, type (.\), type (.+)
  , type (.\/), type (.\\), type (.//)
  , BiForall, Forall, FreeForall, FreeBiForall
  , switch, caseon
  -- * Record Construction
  , empty
  , type (.==), (.==), pattern (:==)
  -- ** Restriction
  , type (.-), (.-)
  -- ** Query
  , type (.!), (.!)
  -- ** Union
  , (.+), Disjoint, pattern (:+)
  , (.//)
  -- * Variant construction
  , pattern IsJust
  -- ** Expansion
  , diversify
  -- ** Destruction
  , impossible, trial, trial', multiTrial
  -- * Labels
  , labels
  )
where

import Data.Row.Dictionaries
import Data.Row.Variants
import Data.Row.Records
import Data.Row.Switch
