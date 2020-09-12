# Overriding Type Class Instances

_April 2020_

_by Daniel Winograd-Cort_


I read a post by Cary Robbins titled
[Overriding Type Class Instances](http://caryrobbins.com/dev/overriding-type-class-instances-2/)
that describes a clever way to derive custom type class instances for types using
some type-level programming tricks and the `DerivingVia` extension.  It struck me
that row-types should be able to do nearly the same thing almost for free, and I
took it as a challenge to see if I could make it work.  It required a minor change
to the library (the addition of a specialized `coerce` function for records), but
otherwise it was quite straightforward.

## Example

<details class="code-details">

<summary>Extensions and imports for this Literate Haskell file</summary>

```haskell
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
module OverridingTypeClassInstances where

-- Note that `Data.Row.Aeson` is not exported my the row-types library and
-- currently lives in the src\aeson directory.  You must put it in an
-- appropriate place and make sure to have `aeson` in your environment in order
-- to use this module.

import           Data.Aeson       (ToJSON(..))
import           Data.Char        (ord, toUpper)
import           Data.Coerce
import           Data.Row
import           Data.Row.Aeson   ()
import qualified Data.Row.Records as Rec
import           Data.Text        (Text)
import qualified Data.Text        as Text
import           GHC.Generics     (Generic)

newtype Uptext = Uptext { unUptext :: Text }

instance ToJSON Uptext where
  toJSON = toJSON . Text.toUpper . unUptext

newtype CharArray = CharArray { unCharArray :: String }

instance ToJSON CharArray where
  toJSON = toJSON . map (:[]) . unCharArray
```
</details>

Cary's result looks like the following:

```haskell
data MyRec = MyRec
  { foo :: Int
  , bar :: String
  , baz :: Text
  } deriving stock (Show, Eq, Generic)
    deriving (ToJSON)
      via Override MyRec
            '[ String `As` CharArray
             , "baz" `As` Uptext
             ]
```

The idea here is that the `MyRec` data type can have a `ToJSON` instance where
all `String` fields are encoded using the `ToJSON` functionality of the `CharArray`
type class and the `baz` field is encoded using the `ToJSON` of `Uptext`.  The
rest of Cary's post describes how he accomplishes this.

With row-types, it's currently not possible to do a wholesale modification based
on types, but we certainly have machinery for modifying individual fields.  Thus
instead, I propose a slightly different syntax, this time based on row-types
operators:

```haskell
data MyRec = MyRec
  { foo :: Int
  , bar :: String
  , baz :: Text
  } deriving stock (Show, Eq, Generic)
    deriving (ToJSON)
      via Override MyRec (
           "bar" .== CharArray
        .+ "baz" .== Uptext)
```

## Details

The `Override` type is actually very simple:

```haskell
newtype Override t (mods :: Row *) = Override { unOverride :: t }
```

A value of type `Override t mods` is a value of type `t` that will have certain
fields overridden according to `mods`.  The key is in how we define the `ToJSON`
instance for `Override`:

```haskell
instance
  ( ρ ≈ Rec.NativeRow t
  , ρ' ≈ mods .// ρ
  , BiForall ρ ρ' Coercible
  , Rec.FromNative t
  , Forall ρ' ToJSON
  ) => ToJSON (Override t mods) where
  toJSON = toJSON . Rec.coerceRec @ρ @ρ' . Rec.fromNative . unOverride
```
This may look a little intimidating, so let's take it piece by piece.  I'll
start with `unOverride` and work through the composed functions, calling out
elements of the context as they become relevant and necessary.

- `unOverride` is the simplest component.  We must unwrap the  `Override` newtype.

- `Rec.fromNative` is a convenient function for converting a native Haskell data
type value into a row-types record.  It produces a record with exactly the same
fields and types as the given record.  For instance, when called on a value of
type `MyRec`, it will produce a value of type
`Rec ("foo" .== Int .+ "bar" .== String .+ "baz" .== Text)`.  In order to do this,
we need the constraint `Rec.FromNative t`, and it additionally provides a type
synonym `Rec.NativeRow t` which will be equal to the row-type produced.   You can
see that in the  instance's context above, we bind the type variable `ρ` to this type.

- `Rec.coerceRec @ρ @ρ'` is a record coercion turning a record with row-type `ρ`
to one of of type `ρ'`.  This will only succeed if all of the types in `ρ` match
up and are coercible with all the types in `ρ'`, a fact that is captured by the
constraint `BiForall ρ ρ' Coercible`.  What is `ρ'`?  It is precisely `ρ`, but
overwritten with any row bindings in `mods` (this is captured in `ρ' ≈ mods .// ρ`).
For example,
`("bar" .== CharArray) .// ("foo" .== Int .+ "bar" .== String .+ "baz" .== Text)`
becomes `("foo" .== Int .+ "bar" .== CharArray .+ "baz" .== Text)`.

- `toJSON` is the `toJSON` function specialized to records with type `ρ'`, and
it requires the constraint `Forall ρ' ToJSON`, indicating that every field in
`ρ'` must have its own `ToJSON` instance.

Phew!  What does that all mean?  It means we can take a value of type `t`, convert
it to a row-types record, coerce any internal types to newtypes with `ToJSON` instances
we prefer, and then produce the JSON of the result all in one go.  And it works!
It's true that the instance definition is a little hairy, but thankfully we don't
need to mess around with any `Generic` code.

## Exploring Overrides

Cary defines an `override` shorthand and then proceeds to demo
some examples.  I'll do the same.

```haskell
-- | A version of 'Override' that accepts first the value and then the mods type.
override :: a -> (forall mods. Override a mods)
override = Override
```

Now we can write statements in GHCi like:

```
> v = MyRec 3 "foo" "text"
> encode $ override v @Empty
{"foo":3,"baz":"text","bar":"foo"}

> encode $ override v @("bar" .== CharArray .+ "baz" .== Uptext)
{"foo":3,"baz":"TEXT","bar":["f","o","o"]}
```

We also get pretty good type errors when we do things wrong.  For instance, if
we try to override the same field more than once:

```
> encode $ override v @("bar" .== CharArray .+ "bar" .== String)
<interactive>:4:1: error:
    • The label "bar" has conflicting assignments.
      Its type is both CharArray and String.
    • In the expression:
        encode $ override v @("bar" .== CharArray .+ "bar" .== String)
      In an equation for ‘it’:
          it
            = encode $ override v @("bar" .== CharArray .+ "bar" .== IntChar)
```

Alternatively, if you try to coerce to a type that's not coercible, you'll get
a good error:

```
> encode $ override v @("bar" .== Int)
<interactive>:5:1: error:
    • Couldn't match representation of type ‘[Char]’ with that of ‘Int’
        arising from a use of ‘encode’
    • In the expression: encode $ override v @("bar" .== Int)
      In an equation for ‘it’: it = encode $ override v @("bar" .== Int)
```

## Achievements and Limitations

With a simple `newtype` and a one-line `ToJSON` instance (the implementation of
the instance is a simple one line, although I'll admit the context takes a few
more), we've been able to recreate most of the expressiveness of
`generic-override`.  Of course, `generic-override` has one feature that we
don't: namely, being able to override all fields of a particular type in one go.
I can definitely see the use for this feature—for instance, making sure _all_
`Text` fields are encoded in a consistent, perhaps more concise, way—but I don't
see a way to do it elegantly with row-types at this time.<sup>[1](#myfootnote1)</sup>

But we do gain for what we've given up.  Without needing a `ValidateOverride`
type class, we have clear restrictions (and informative error messages) that
prevent us from duplicate overriding.  Additionally, we of course have all the
other benefits of row-types.

---

<a name="myfootnote1">1</a>: If/When GHC adopts the ability to use simple, unsaturated
type families, this will become possible.  For instance, one could write something like
```haskell
type family ToUptext t where
  ToUptext Text = Uptext
  ToUptext x = x
```
and then make the override modifications: `Rec.Map ToUptext (Rec.NativeRow MyRec)`.
This in itself is still slightly ugly, but unsaturated type families give us the
ability to write more higher-order type functions, such as a row-types `Filter`.
From there, it's a brief hop to a type-level function `FieldsOfTo MyRec Text Uptext`
which would produce a row-type containing all of the fields of `MyRec` that had
the type `Text`, now with the type `Uptext`.  Just `.+` that with any other
type modifications you want to make, and you're all set.
