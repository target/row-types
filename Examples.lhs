
> module Examples where
>
> import Data.OpenRecords.Records
> import Data.OpenRecords.Variants
> import Data.Proxy

In this example file, we will explore how to create and use records and variants.

To begin, we will declare a few label names that we can use throughout.

> x = Label :: Label "x"
> y = Label :: Label "y"
> z = Label :: Label "z"
> w = Label :: Label "w"

Note that with type applications, it is also fine to write:

> name = Label @"name"

--------------------------------------------------------------------------------
  RECORDS
--------------------------------------------------------------------------------

With some labels defined, let's begin with records.  To start, let's create a
record representing the Cartesian coordinates of the origin.  To do this,
we use the := operator to initialize values in a record, and we separate each
initialized value with the .| operator.  We're creating a record from scratch
rather than extending an already existing one, so after the initialization, we
write empty.

> origin :: Rec ("x" :== Double :+ "y" :== Double )
> origin = x .= 0 .+ y .= 0

Note that, although we wrote the type explicitly, GHC has no problem inferring
it exactly.  Also note that the type follows the same form as the value.  Instead
of using the label x, we use the type level symbol "x", the 0 values are replaced
with their types (Double), and the operators := and .| are replaced with type level
versions ::= and :|.

If we show this at the repl, we see:
λ> origin
{ x=0.0, y=0.0 }

Of course, as an extensible record, the order that we build it shouldn't matter,
and indeed, it doesn't.  Consider the following variation:

> origin' :: Rec ("y" :== Double :+ "x" :== Double)
> origin' = y .= 0 .+ x .= 0

If we show this at the repl, we see:

λ> origin2
{ x=0.0, y=0.0 }

Indeed, the two values are indistinguishable:

λ> origin == origin'
True

Now, let's expand upon our record.  Why stop at two dimensions when we can make
a record in three dimensions.

> origin3D = z .= 0.0 .+ origin

Once again, the type is inferred for us, and the record is exactly as expected.

In fact, we can do this generally.  The following function takes a name and a
record and adds the "name" field to that record with the given name.

> named :: r :\ "name" => a -> Rec r -> Rec ("name" :== a :+ r)
> named s r = name .= s .+ r

Note that we require that the record we are naming must not have a "name" field
already.  Overlapping labels within a single record/variant is strictly forbidden.

Let's say we want to get the values out of the record.  Simple selection is achieved
with the .! operator, like so:

λ> origin .! x
0.0

and we can use this to write whatever we want.  Here is a function for calculating
Euclidean distance from the origin to a point:

> distance :: (Floating t, (r :! "y") ~ t, (r :! "x") ~ t) => Rec r -> t
> distance p = sqrt $ p.!x * p.!x + p.!y * p.!y

Once again, the type of distance is entirely inferrable, but we write it here for
convenience.  This works exactly as expected:

λ> distance origin
0.0
λ> distance origin3D
0.0
λ> distance (named "2D" origin)
0.0

Of course, that wasn't very interesting when our only points are at the origin
already.  We could make new records representing new points, but instead, let's
write a function to move the points we have:

> move :: (Num (r :! "x"), Num (r :! "y"))
>      => Rec r -> r :! "x" -> r :! "y" -> Rec r
> move p dx dy = x :<- p.!x + dx .|
>                y :<- p.!y + dy .| p

Here, we're using the update operator :<- to update the value at the label x with
the value at x plus the given dx, and then we do the same for y.  We string these
updated together using the .| operator, and as these are modifications, we finally
indicate what record we should be modifying: p.  We can see it work in practice:

λ> move origin 3 4
{ x=3.0, y=4.0 }
λ> distance (move origin 3 4)
5.0
λ> distance (move (named "2D" origin3D) 5 12)
13.0

So far, we created an origin point in 2d and then one in 3d, but what if we are
adventurous mathematicians who want to have points in a space with some arbitrary
number of dimensions.  We could write out each of the 0s necessary, but there's
an easier way to initialize a record:

> origin4 :: Rec ("x" :== Double :+ "y" :== Double :+ "z" :== Double :+ "w" :== Double)
> origin4 = rinit (Proxy @Num) 0

Finally, we have come to a case where GHC cannot infer the type signature, and how
could it!  The type is providing crucial information about the shape of the record.
Regardless, with the type provided, it works exactly as expected:

λ> origin4
{ w=0.0, x=0.0, y=0.0, z=0.0 }


--------------------------------------------------------------------------------
  VARIANTS
--------------------------------------------------------------------------------
Let's move on from records to variants.  In many ways, variants are quite similar,
as might be expected given that variants are dual to records.  The types look
almost the same, and some of the operators are shared as well.  However,
construction and destruction are obviously different.

Creating a variant can be done with just:

> v,v' :: Var ("y" :== String :+ "x" :== Integer)
> v  = just x 1
> v' = just y "Foo"

Here, the type is necessary to specify what concrete type the variant is (when
using AllowAmbiguousTypes, the type is not always needed, but it would be needed
to e.g. show the variant).  In the simple case of a variant of just one type,
the simpler just' function can be used:

> v2 = just' x 1

Now, the type can be easily derived by GHC.  We can show variants as easily as
records:

λ> v
{x=1}
λ> v'
{y="Foo"}
λ> v2
{y=1}

Once created, a variant can be expanded by using the same extend function that
can be used on records, except that instead of providing a value for the new
label being added, one merely needs to provide a Proxy of the value.

> v3 = extend y (Proxy @String) v2

Of course, showing v2 will look the same as showing v3, but the types are actually
different.  Indeed, it is a type error to try to check whether they're equal:

λ> v2 == v3
error:
    • Couldn't match type ‘'["y" ':-> [Char]]’ with ‘'[]’
      Expected type: Var ('R '["x" ':-> Integer])
        Actual type: Var (Extend "y" String ('R '["x" ':-> Integer]))
    • In the second argument of ‘(==)’, namely ‘v3’
      In the expression: v2 == v3
      In an equation for ‘it’: it = v2 == v3

This may look a little scary, but it's actually a pretty useful message.  Essentially,
it's expecting a variant that can only be an Integer at label "x", but it found one
that could also be a String at label "y".  So, comparing v2 and v3 is not allowed,
but since v3 now has the same labels as v1, that comparison is fine:

λ> v == v3
True
λ> v == just x 3
False
λ> v == v'
False
λ> v == just y "fail"
False

(Also note here that using just without a type signature is fine because the correct
type can be easily inferred due to v's type.)

What can you do with a variant?  The only way to really use one is to get the value
out, and to do that, you must trial it:

λ> trial v x
Left 1
λ> trial v y
Right {x=1}
λ> trial v' x
Right {y="Foo"}
λ> trial v' y
Left "Foo"

If trialing at a label l succeeds, then it provides a Left value of the value at l.
If not, it provides a Right value of the variant with this label removed---since the
trial failed, we now can be sure that the value is not from l.

For ease of use in view patterns, Variants also exposes the viewV function.  With
it, we can write a function like this:

> myShow :: ((r :! "y") ~ String, Show (r :! "x")) => Var r -> String
> myShow (viewV x -> Just n) = "Int of "++show n
> myShow (viewV y -> Just s) = "String of "++s
> myShow _ = "Unknown"

λ> myShow v
"Int of 1"
λ> myShow v'
"String of Foo"

Once again, the type signature is totally derivable.

There are two minor warts with this.  First, it's fairly common to want to define
a function like myShow to be exhaustive in the variant's cases, but to do this,
you must manually provide a type signature:

> myShowRestricted :: Var ("y" :== String :+ "x" :== Integer) -> String
> myShowRestricted (viewV x -> Just n) = "Int of "++show n
> myShowRestricted (viewV y -> Just s) = "String of "++s
> myShowRestricted _ = error "Unreachable"

The second blemish can be seen in this restricted version of myShow.  Even though
we know from the type that we've covered all the posibilities of the variant, GHC
will generate a "non-exhaustive pattern match" warning without the final line.

Another common case is when you have a variant, and you want to convert it into
one with a different type signature.  There are two ways to do this.  If the new
type is strictly more general than the current one, you can diversify your variant.
Essentially, this works by unwrapping the underlying value and then calling just
on it so it has the right type.

λ> diversify @("y" :== String) v2 == v3
True

GHC is not quite clever enough to infer the right thing without a type annotation
here.





