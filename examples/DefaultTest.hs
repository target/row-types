{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module DefaultTest where

import Data.Row
import qualified Data.Row.Records as Row
import GHC.Generics

type CompanyId = Int

data Company = Company
  { companyName :: String
  } deriving (Show, Eq, Generic)

type ProductId = Int

data Product = Product
  { productName :: String
  , productCompanyId :: CompanyId
  } deriving (Show, Eq, Generic)

buildName :: IO String
buildName = pure "Fancy Generated Name"

type BuildCompany = "name" .== Maybe String

defCompany :: Rec BuildCompany
defCompany = #name .== Nothing

buildCompany :: Rec BuildCompany -> IO Company
buildCompany ps = do
  companyName <- fromParams (ps .! #name) buildName
  pure $ Company {..}

type BuildProduct = "name" .== Maybe String .+ "companyId" .== Maybe CompanyId .+ "company" .== Rec BuildCompany

defProduct :: Rec BuildProduct
defProduct = #name .== Nothing .+ #companyId .== Nothing .+ #company .== defCompany

buildProduct ::
  Rec BuildProduct -> IO Product
buildProduct ps = do
  productName <- fromParams (ps .! #name) buildName
  productCompanyId <- fromParamsIns (ps .! #companyId) (buildCompany (ps .! #company))
  pure $ Product {..}

-- | think persistent's `insert` here, returning record id
insertInDb :: Show a => a -> IO Int
insertInDb a = putStrLn (show a) >> pure 1

fromParams :: Applicative f => Maybe a -> f a -> f a
fromParams mv builder = do
  case mv of
    Nothing -> builder
    Just v -> pure v

fromParamsIns :: Show a => Maybe Int -> IO a -> IO Int
fromParamsIns mv builder = do
  case mv of
    Nothing -> do
      v <- builder
      insertInDb v
    Just v -> pure v

main :: IO ()
main = do
  product' <-
    buildProduct (
      (  #name .== Just "awesome product"
      .+ #company .== (
          (#name .== Just "awesome company")
        .// defCompany))
    .// defProduct)
  print product'
