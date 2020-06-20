# Typed Errors

_April 2019_

_by Daniel Winograd-Cort_


I read a post by Matt Parsons called
[The Trouble with Typed Errors](https://www.parsonsmatt.org/2018/11/03/trouble_with_typed_errors.html)
that talks about the difficulties we face in Haskell
from not having open variant types.  Matt says:

> Haskell doesn’t have open variants, and the attempts to mock them end up quite
> clumsy to use in practice.

But, I disagree.  I think row-types handles the typed error case quite nicely.

## Imports

As this is a Literate Haskell file, let's get the imports and pragmas out of the
way first...

```haskell
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module TypedErrors where

import Data.Row
```

## Example

I'll try to set up the situation similar to how Matt sets it up in his blog.
Let's start with two functions, `foo` and `bar`, that may each fail.

```haskell
data FooErr = FooErr Int
  deriving (Show)

data BarErr = BarErr String
  deriving (Show)

foo :: Either FooErr Int
foo = Left (FooErr 3)

bar :: Either BarErr Int
bar = Left (BarErr "Oops")
```

Of course, the problem with this code is that there's no good way to deal with
these two errors together.  Matt explains in his blog the various problems, but
in short:

- As is, `foo` and `bar` aren't in the same monad (because they have different
  error types!), so we cannot use do notation.

- If we group the errors into something like `Either FooErr BarErr`, then not
  only must we be very diligent about `Left`s and `Right`s (especially if we add
  more error types), but we run into issues because `Either FooErr BarErr` ≠
  `Either BarErr FooErr`.

- If we combine the errors into one monolithic error type, we lose static
  guarantees about exactly which errors a function may produce and exactly which
  we are handling when we write error handlers.

## A row-types solution

### Generating Errors

With row-types, we have open variants easily available to us, which means we can
do the following:

```haskell
foo :: (AllUniqueLabels r, r .! "fooErr" ≈ Int)    => Either (Var r) Int
foo = Left (IsJust #fooErr 3)

bar :: (AllUniqueLabels r, r .! "barErr" ≈ String) => Either (Var r) Int
bar = Left (IsJust #barErr "Oops")

baz :: (AllUniqueLabels r, r .! "bazErr" ≈ Bool)   => Either (Var r) Int
baz = Left (IsJust #bazErr True)


foobarbaz
  :: ( AllUniqueLabels r
     , r .! "fooErr" ≈ Int
     , r .! "barErr" ≈ String
     , r .! "bazErr" ≈ Bool)
  => Either (Var r) Int
foobarbaz = bar *> foo *> bar *> baz
```

In `foo`, we create error data with the expression `IsJust #fooErr 3`.  This
creates a new row-types variant at the label `"fooErr"` with the value `3`.
The context indicates that the error type may have other possibilities:
specifically, `AllUniqueLabels r` is some boilerplate that guarantees that no
two possibilities have the same name, and `r .! "fooErr" ≈ Int` declares that
the `fooErr` possibility has a payload of type `Int`.

We can do the same for `bar`/`barErr` and `baz`/`bazErr`, and then if we want to
compose them together, we can easily do so as in `foobarbaz`.
Furthermore, although we provide the type signatures here, GHC will infer them
just fine (with `NoMonomorphismRestriction`).

### Handling Errors
We can handle these errors in multiple ways.

First off, it's easy enough to `show` our value (so long as the data in the errors
is `Show`able):

```haskell
printFoobarbaz :: String
printFoobarbaz = show specificFoobarbaz
  where specificFoobarbaz :: Either (Var ("fooErr" .== Int
                                       .+ "barErr" .== String
                                       .+ "bazErr" .== Bool)) Int
        specificFoobarbaz = foobarbaz
```

All row-types variants implement an obvious `Show` instance, but do note that to `show`
`foobarbaz`, we must specify its type.  This is because `foobarbaz` is defined
polymorphically over any variant that has appropriate entries for `fooErr`, `barErr`,
and `bazErr`, but to `show` it, we must pick a concrete type to use for the `Show`
instance.  In this case, we pick the minimum variant.

We can also deal with a single error at a time using the `trial` function.  This
function lets us pluck a particular possibility out of a variant, allowing us
to handle that possibility or be left with the leftovers of the variant.  In the
following case, we handle the `fooErr` possibility, using the `Int` value it
contains as our return value.  If `foobarbaz` is not a `fooErr`, then we're left
with a `Left` error value that cannot be a `fooErr`.

```haskell
handleFoo :: forall r.
  ( AllUniqueLabels r
  , r .! "fooErr" ≈ Int
  , r .! "barErr" ≈ String
  , r .! "bazErr" ≈ Bool)
  => Either (Var (r .- "fooErr")) Int
handleFoo =
  case foobarbaz of
    Left err  -> case trial @_ @r err #fooErr of
      Left  i     -> Right i
      Right other -> Left other
    Right i   -> Right i
```

The type signature of `handleFoo` is a little disappointing but necessary because
we're keeping our variant type entirely polymorphic.  However, if we were willing
to monomorphize our error to a concrete type, the constraints (and the type
applications on `trial`) would no longer be necessary.  This is a tradeoff that
one needs to make based on the situation.

Finally, we have the option of handling all errors at once using `switch`.

```haskell
handleAll :: String
handleAll =
  case foobarbaz of
    Left err -> switch err $
         #fooErr .== (\n -> "FooErr of " ++ show n)
      .+ #barErr .== (\s -> "BarErr of " ++ s)
      .+ #bazErr .== (\b -> "BazErr of " ++ show b)
    Right i  -> "Got the result " <> show i
```

Specifically, `switch` allows us to define a case for every possibility of a
variant, allowing us to reduce the variant to an ordinary result.  In this case,
type annotations are not needed because the variant must match exactly the form
of the `switch`'s cases.  Because we have exactly 3 cases, one for each of our
errors, GHC monomorphizes the error component of `foobarbaz` to
`Var ("fooErr" .== Int .+ "barErr" .== String .+ "bazErr" .== Bool)` automatically.


## Achievements and Limitations

Using variants, we are able to create and handle typed errors without dealing with
weird nesting of `Either`s and without losing any static guarantees.  Furthermore,
variant typed errors can be easily defined with constraints (as we did here with
the constraints like `r .! "fooErr" ≈ Int`) with minimal boilerplate: no extra
data declarations necessary!  And, once monomorphized, two variants with the same
possibilities always share the same type, regardless of the order that the
possibilities are described in the type.  I also didn't discuss `diversify`,
which allows one to expand the possibilities in a variant, which, for typed
errors, allows one to use a limited (perhaps already monomorphized) error type
in a more general setting.

However, there are downsides to variants typed errors.  A little bit of boilerplate
does remain in the form of the `AllUniqueLabels` constraint, which just about always
needs to be used.  Also, GHC has trouble inferring all the types and constraints
when we want to remain as polymorphic as possible, which means writing out some
annoying types and occasionally using type annotations (as seen in `handleFoo`
above).  Lastly, the `switch` expression seems a lot like an ordinary Haskell
`case` expression, but it isn't, which means the user is forced to learn what
amounts to a special syntax just for dispatching the errors.

There are specific considerations for any project, but I think row-types variants
are a great choice for typed errors.
