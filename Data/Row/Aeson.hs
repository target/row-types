{-# LANGUAGE OverloadedStrings #-}
module Data.Row.Aeson () where

import           Data.Aeson
import           Data.Aeson.Encoding (pairStr, pairs)
import           Data.Aeson.Types    (typeMismatch)
import           Data.List           (intercalate)
import           Data.Text           (Text)
import qualified Data.Text           as Text (pack)

import           Data.Row
import qualified Data.Row.Records  as Rec
import qualified Data.Row.Variants as Var

instance Forall r ToJSON => ToJSON (Rec r) where
  toJSON = Object . Rec.eraseToHashMap @ToJSON toJSON

  toEncoding =
    pairs . foldMap (uncurry pairStr) . Rec.eraseWithLabels @ToJSON toEncoding

instance (AllUniqueLabels r, Forall r FromJSON) => FromJSON (Rec r) where
  parseJSON (Object o) = do
    r <- Rec.fromLabelsA @FromJSON $ \ l -> do x <- o .: (show' l)
                                               x `seq` pure x
    r `seq` pure r

  parseJSON v = typeMismatch msg v
    where msg = "REC: {" ++ intercalate "," (labels @r @FromJSON) ++ "}"

instance Forall r ToJSON => ToJSON (Var r) where
  toJSON v = object [foo l]
    where (l, foo) = Var.eraseWithLabels @ToJSON (\v l -> l .= v) v

instance (AllUniqueLabels r, Forall r FromJSON) => FromJSON (Var r) where
  parseJSON (Object o) = Var.fromLabels @FromJSON $ \ l -> o .: (show' l)
  parseJSON v = typeMismatch msg v
    where msg = "VAR: {" ++ intercalate "," (labels @r @FromJSON) ++ "}"

show' :: Show a => a -> Text
show' = Text.pack . show
