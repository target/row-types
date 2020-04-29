{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
module RowCSV where

import GHC.Generics (Generic)

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L
import Text.Read (readMaybe)

import Data.Row
import qualified Data.Row.Records as Rec


data PL = PL
  { name   :: Text
  , year   :: Int
  , person :: Text
  } deriving (Eq, Ord, Show, Generic)


type PLRow = "name" .== Text .+ "year" .== Int .+ "person" .== Text


pls :: [PL]
pls =
    [ PL "Haskell" 1990 "Simon"
    , PL "Scala"   2004 "Martin"
    , PL "Idris"   2009 "Edwin"
    , PL "Perl"    1987 "Larry"
    ]


rowPLs :: [Rec PLRow]
rowPLs = Rec.fromNative <$> pls


input :: Text
input = T.unlines
    [ "year,name,types,person,website"
    , "1987,Perl,no,Larry"
    , "1990,Haskell,nice,Simon,https://www.haskell.org/"
    , "2004,Scala,weird,Martin,https://www.scala-lang.org/"
    , "2009,Idris,fancy,Edwin,https://www.idris-lang.org/"
    ]


class    ToField a    where toField :: a -> Text
instance ToField Text where toField = id
instance ToField Int  where toField = T.pack . show


recToCSV :: forall ρ. Forall ρ ToField => [Rec ρ] -> Text
recToCSV rs = T.unlines $ map (T.intercalate ",")
  $ Rec.labels @ρ @ToField
  : map (Rec.erase @ToField toField) rs


toCSV :: forall ρ t. (Rec.FromNative t, Rec.NativeRow t ≈ ρ, Forall ρ ToField) => [t] -> Text
toCSV = recToCSV @ρ . fmap Rec.fromNative


class    FromField a    where fromField :: Text -> Either String a
instance FromField Text where fromField = Right
instance FromField Int  where
  fromField t =
    maybe (Left $ "Invalid Int: " ++ show t) Right $ readMaybe $ T.unpack t


recFromCSV :: forall ρ. (AllUniqueLabels ρ, Forall ρ FromField)
           => Text -> Either String [Rec ρ]
recFromCSV s = case map (T.splitOn ",") (T.lines s) of
  [] -> Left "No Input"
  header:vals -> traverse makeRecord vals
    where
      makeRecord s = Rec.fromLabelsA @FromField @(Either String) @ρ (makeField s)
      makeField :: (KnownSymbol l, FromField a) => [Text] -> Label l -> Either String a
      makeField val l =
        maybe (Left $ "Missing field " ++ show l) fromField $
          L.lookup (T.pack $ show l) (zip header val)


fromCSV :: forall t ρ. (Rec.ToNative t, ρ ≈ Rec.NativeRow t, AllUniqueLabels ρ, Forall ρ FromField)
        => Text -> Either String [t]
fromCSV = fmap (fmap Rec.toNative) . recFromCSV @ρ


main = case fromCSV @PL input of
    Left err -> putStrLn $ "ERROR: " ++ err
    Right xs -> mapM_ print xs
