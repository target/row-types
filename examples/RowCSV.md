# Row types for CSV library
_July 2019_

_by Daniel Winograd-Cort_

## Introduction

Oleg Grenrus wrote a recent post titled
["Fancy types for CSV library"](http://oleg.fi/gists/posts/2019-07-15-fancy-types-for-cassava.html).
In it, he shows how to use vectors and other _fancy types_ to make CSV encoding and
decoding more type safe (as compared to `cassava`).  It's a clever idea that uses
an ordered vector of encoded fields (with length at the type level) as an intermediate
data type.  Thus, for encoding, one encodes their chosen data types into these vectors
and then encodes the vectors into csv text.  For decoding, one decodes the csv text
into vectors and then decodes those vectors into the data types.  Some trouble arises
during decoding---perhaps the order of values in the csv input is different from
the order in the data type, or perhaps there are missing fields in the csv input---and
Oleg describes some nice tricks to deal with these problems.

At the end of the article, Oleg writes:

> One valid question to ask, is whether row-types would simplify something here.
> Not really.
>
> For example vinyl's Rec type is essentially the same as NP. Even if there were
> anonymous records in Haskell, so toRecord could be implemented directly using a
> built-in function, it would remove only a single problem from many. At it's not
> much, as toRecord is generically derivable.

I disagree with this conclusion, and in this post, I'll show how simple the whole
process of csv encoding and decoding can be with the row-types library.  In fact,
not only is the code short and clear, but it has even more type safety than Oleg's
version.

## Example

<details class="code-details">

<summary>Extensions and imports for this Literate Haskell file</summary>

```haskell

{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
module RowCSV where

import GHC.Generics (Generic)

import Data.Text (Text)
import qualified Data.Text    as T
import qualified Data.Text.IO as T
import qualified Data.List    as L
import Text.Read (readMaybe)

import Data.Row
import qualified Data.Row.Records as Rec
```
</details>

I'll start with the same data that Oleg uses:

```haskell
data PL = PL
  { name   :: Text
  , year   :: Int
  , person :: Text
  } deriving (Eq, Ord, Show, Generic)

pls :: [PL]
pls =
    [ PL "Haskell" 1990 "Simon"
    , PL "Scala"   2004 "Martin"
    , PL "Idris"   2009 "Edwin"
    , PL "Perl"    1987 "Larry"
    ]

input :: Text
input = T.unlines
    [ "year,name,types,person,website"
    , "1987,Perl,no,Larry"
    , "1990,Haskell,nice,Simon,https://www.haskell.org/"
    , "2004,Scala,weird,Martin,https://www.scala-lang.org/"
    , "2009,Idris,fancy,Edwin,https://www.idris-lang.org/"
    ]
```

Here we have a simple record of programming language information.  We have a list
of a few languages, and we also have a sample CSV input.  Note that the CSV input
has extra fields, and it even has a missing website fields for one of the entries.
We will see that since the `PL` type doesn't have a `website` field, it won't matter
that the CSV data is missing that field.

## Encoding to CSV

I'm going to follow Oleg's plan pretty closely, but instead of using vectors of
`Text` as the intermediate value, I'll be using an extensible row-types record.  
It's very easy to convert the `PL` type into an row-types record: use the
built-in `fromNative`.  For instance:

```
*Main> :t Rec.fromNative <$> pls
Rec.fromNative <$> pls
  :: [Rec ("name" .== Text .+ "person" .== Text .+ "year" .== Int)]
*Main> Rec.fromNative <$> pls
[#name .== "Haskell" .+ #person .== "Simon" .+ #year .== 1990,#name .== "Scala" .+ #person .== "Martin" .+ #year .== 2004,#name .== "Idris" .+ #person .== "Edwin" .+ #year .== 2009,#name .== "Perl" .+ #person .== "Larry" .+ #year .== 1987]
```

The ordering in row-types comes down to lexicographical ordering
by field name, which is why it's different here than in `PL`, but it's not something
we need to worry about because row-types are automatically normalized.

For the individual fields, let's use the same `ToField` class that Oleg uses:

```haskell
class    ToField a    where toField :: a -> Text
instance ToField Text where toField = id
instance ToField Int  where toField = T.pack . show
```

And now, because we're using row-types as our intermediate data type, we are
ready to produce CSV data:

```haskell
recToCSV :: forall ρ. Forall ρ ToField => [Rec ρ] -> Text
recToCSV rs = T.unlines $ map (T.intercalate ",")
  $ Rec.labels @ρ @ToField
  : map (Rec.erase @ToField toField) rs
```

Let's walk through this line by line.  The first line is the type signature, where
we demand that each field of the row-type `ρ` have a `ToField` instance.  The second
line should look pretty familiar: we stick commas between fields and turn a list of
`Text`s into a `Text`.  In the third line, we create the CSV header; the function `labels`
returns the field names of a row type, and it only needs type arguments to work.
The last line is where the individual records are encoded.  The `erase` function is
applied to each record in the input list; `erase` erases the field name information
and maps the given function over the values, returning a simple list of results.

Lastly, we can make a general `toCSV` function by composing `fromNative` and `recToCSV`:

```haskell
toCSV :: forall ρ t. (Forall ρ ToField, Rec.FromNative t ρ) => [t] -> Text
toCSV = recToCSV @ρ . fmap Rec.fromNative
```

We can do a sanity check with:

```
*Main> T.putStr $ toCSV pls
name,year,person
Haskell,1990,Simon
Scala,2004,Martin
Idris,2009,Edwin
Perl,1987,Larry
```

## Decoding from CSV

Once again, we'll use the same field conversion functions as Oleg:

```haskell
class    FromField a    where fromField :: Text -> Either String a
instance FromField Text where fromField = Right
instance FromField Int  where
  fromField t =
    maybe (Left $ "Invalid Int: " ++ show t) Right $ readMaybe $ T.unpack t
```

And with just this class, we're immediately ready to parse the csv data:

```haskell
recFromCSV :: forall ρ. (AllUniqueLabels ρ, Forall ρ FromField) => Text -> Either String [Rec ρ]
recFromCSV s = case map (T.splitOn ",") (T.lines s) of
  [] -> Left "No Input"
  header:vals -> sequence $ makeRecord <$> vals
    where
      makeRecord s = Rec.fromLabelsA @FromField @(Either String) @ρ (makeField s)
      makeField :: (KnownSymbol l, FromField a) => [Text] -> Label l -> Either String a
      makeField val l = let lookupList = zip header val
        in maybe (Left $ "Missing field " ++ show l) fromField $ L.lookup (T.pack $ show l) lookupList
```
Let's walk through this one line by line too.
In the type signature, we're demanding that the extensible record that we're parsing
have unique labels for every field---it wouldn't make sense to have two different
fields with the same name---and that each field has a `FromField` instance.
The second line is just dealing with commas and lines, and the third line is dealing
with bad input.
On the fourth line, we separate the header from the rest of the lines.  We then call
the inner function `makeRecord` on each of the lines and sequence the results.
The sixth line defines `makeRecord`, which uses the `fromLabelsA` (`A` for Applicative)
functions to construct a row-type record based on its field names.  This in turn
uses the `makeField` function, which takes the csv line and the label and returns
either a `Left` error message if parsing fails or a `Right` value if it succeeds.
Parsing is simply looking  up the field name (`T.pack $ show l`) in the line and
calling `fromField` on it.

Of course, we could probably do something smarter here than doing a lookup in a
linked list---using a `Map` comes to mind---but we're going for simplicity over
efficiency for now.

Lastly, we can convert a value of type `Rec ρ` to a native Haskell data type with
the row-types built-in `toNative`.  (We will go one step further and use the restricted
function `toNativeExact`, which forces the record to have the exact same fields as
the native data type, because this helps with type inference.)
This lets us write a general `fromCSV` function:

```haskell
fromCSV :: forall t ρ.
  (AllUniqueLabels ρ, Forall ρ FromField, Rec.ToNativeExact t ρ)
  => Text -> Either String [t]
fromCSV = fmap (fmap Rec.toNativeExact) . recFromCSV @ρ
```

We can do a sanity check with:

```
main :: IO ()
main = case fromCSV @PL input of
  Left err -> putStrLn $ "ERROR: " ++ err
  Right xs -> mapM_ print xs

*Main> main
PL {name = "Perl", year = 1987, person = "Larry"}
PL {name = "Haskell", year = 1990, person = "Simon"}
PL {name = "Scala", year = 2004, person = "Martin"}
PL {name = "Idris", year = 2009, person = "Edwin"}
```

## The Difficult Part

There isn't one!  Notice that our first implementation of `recFromCSV` was perfectly
able to handle data with missing fields and reordered columns, and it didn't
require any extra work on our part.

## Conclusions and Extensions

Oleg claims that row-types would not simplify anything in CSV encoding and decoding,
but I must disagree.  Not only did the row-types library give us free `fromNative`
and `toNative` functions and heterogeneous type safety, but it handled all of the
difficult cases of missing data and reordered columns for free as well.

Furthermore, if one thinks of the row-type record as an intermediate data type as
described in the introduction, then we can extend this CSV parsing to incorporate the
ideas of [type surgery](TypeSurgery.html) as well.  Instead of needing
a `FromField` class, one could very simply lift the `Text` from the CSV into structured
records and then do surgery on them from there.
