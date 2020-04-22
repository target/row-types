
-- Based on https://chrispenner.ca/posts/hkd-options

import Control.Applicative
import Data.Row
import qualified Data.Row.Internal as Row
import qualified Data.Row.Records as Rec

import System.Environment (lookupEnv, setEnv)
import Text.Read (readMaybe)

type OptionsRow =
     "serverHost" .== String
  .+ "numThreads" .== Int
  .+ "verbosity"  .== Int



--
readEnv :: Read a => String -> IO (Maybe a)
readEnv envKey = do
    lookupEnv envKey >>= pure . \case
        Just x -> readMaybe x
        Nothing -> Nothing

-- No need to use `Compose`
envOpts' :: Rec (Rec.Map IO (Rec.Map Maybe OptionsRow))
envOpts' =
     #serverHost .== readEnv "SERVER_HOST"
  .+ #numThreads .== readEnv "NUM_THREADS"
  .+ #verbosity  .== pure Nothing -- Don't read verbosity from environment

envOpts :: IO (Rec (Rec.Map Maybe OptionsRow))
envOpts =  Rec.sequence @IO $
     #serverHost .== readEnv "SERVER_HOST"
  .+ #numThreads .== readEnv "NUM_THREADS"
  .+ #verbosity  .== pure Nothing -- Don't read verbosity from environment


-- Once again, no need for Compose
-- jsonOptsCustom :: A.Value -> Rec (Rec.Map Maybe OptionsRow)
-- jsonOptsCustom = Rec.sequence @((->) A.Value) $
--      #serverHost .== (preview $ key "host"        . _String . unpacked)
--   .+ #numThreads .== (preview $ key "num_threads" . _Number . to round)
--   .+ #verbosity  .== (preview $ key "verbosity"   . _Number . to round)


-- The following commented out section is full of failed attempts at helper
-- functions for zipping.  What I really need is the ability to have unsaturated
-- type families, so I can write a type level const function that gets applied
-- during the zip.  In other words, once https://github.com/ghc-proposals/ghc-proposals/pull/242
-- is accepted, I should be able to rewrite some internals of row-types and
-- finish this.
{-
myFun :: forall a. (Row.IsA Row.Unconstrained1 Maybe a) => a -> a -> Pair a a
myFun a b = case Row.as @Row.Unconstrained1 @Maybe @a of
  Row.As -> Pair $ a <|> b


class (Row.IsA Row.Unconstrained1 Maybe a, a ~ b) => MyConstraint a b
instance (Row.IsA Row.Unconstrained1 Maybe a, a ~ b) => MyConstraint a b

data Pair x y = Pair y

class PairX y where
  unPairX :: forall x. Pair x y -> y
instance PairX y where
  unPairX (Pair y) = y

class (forall y. PairX y ~ a) => UnPair a
instance (forall y. PairX y ~ a) => UnPair a
-}



type family Fst a b :: * where
  Fst a b = a

--
getOptions :: IO (Rec (Rec.Map Maybe OptionsRow))
getOptions = do
    -- configJson <- readConfigFile
    envOptsRec <- envOpts
    envOptsRec2 <- envOpts
    let zippedRec :: Rec (Rec.ZipWith Pair (Rec.Map Maybe OptionsRow) (Rec.Map Maybe OptionsRow))
    -- let zippedRec :: Rec (Rec.Map Maybe OptionsRow)
        zippedRec = Rec.zipWith @MyConstraint @Pair myFun envOptsRec envOptsRec2
    -- let zippedRec :: Rec ZippedMaybeOptionsRow
    --     zippedRec = Rec.zip envOptsRec envOptsRec2
    --     joinedRec :: Rec (Rec.Map Pair ZippedMaybeOptionsRow)
    --     joinedRec = Rec.map @IsSamePairOf @Pair @ZippedMaybeOptionsRow (Pair . joinPair) zippedRec
    --     sequencedRec :: _
    --     sequencedRec = Rec.sequence @Pair @ZippedMaybeOptionsRow joinedRec
    return undefined
