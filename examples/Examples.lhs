> {-# LANGUAGE OverloadedLabels #-}
> {-# LANGUAGE DeriveGeneric #-}
> {-# LANGUAGE PartialTypeSignatures #-}
> module Examples where
>
> import Data.Row
> import qualified Data.Row.Records as Rec
> import qualified Data.Row.Variants as Var

In this example file, we will explore how to create and use records and variants.

--------------------------------------------------------------------------------
  LABELS
--------------------------------------------------------------------------------

To begin, we will briefly discuss creating labels -- their use will follow.

The most basic way to create a label is through construction with a type signature:

 x = Label :: Label "x"

With the above definition, x is a label for the field x.  Using type applications,
this can be shortened to:

 x = Label @"x"

And with OverloadedLabels, one can just write:

 #x

We will use the OverloadedLabels notation in these examples.

--------------------------------------------------------------------------------
  LENS
--------------------------------------------------------------------------------

Records and variants play nicely with the lens library if we additionally import
Data.Row.Lens from the row-types-lens "orphan instance" library.  Each overloaded
label is also a Lens for a record and a Traversal for variants.  Thus, .! can be
replaced with ^. and trial can be made infix with ^?.  Additionally, update
can be made infix:

update #x v r === r & #x .~ v

And because of the power of lens, it's easy to make modifications rather than
just update:

update #x (f $ r .! #x) r === r & #x %~ f

Lens is not included with row-types by default, but using it can make row-types
much friendlier.

--------------------------------------------------------------------------------
  RECORDS
--------------------------------------------------------------------------------

With some labels defined, let's begin with records.  To start, let's create a
record representing the Cartesian coordinates of the origin.  To do this,
we use the .== operator to initialize values in a record, and we separate each
initialized value with the .+ operator.Notice that the value level code uses the
same operators as the type level code.

> origin :: Rec ("x" .== Double .+ "y" .== Double )
> origin = #x .== 0 .+ #y .== 0

Note that, although we wrote the type explicitly, GHC has no problem inferring
it exactly.

If we show this at the repl, we see:
λ> origin
 #x .== 0.0 .+ #y .== 0.0

Of course, as an extensible record, the order that we build it shouldn't matter,
and indeed, it doesn't.  Consider the following variation:

> origin' :: Rec ("y" .== Double .+ "x" .== Double)
> origin' = #y .== 0 .+ #x .== 0

If we show this at the repl, we see:

λ> origin'
 #x .== 0.0 .+ #y .== 0.0

Indeed, the two values are indistinguishable:

λ> origin == origin'
True

Now, let's expand upon our record.  Why stop at two dimensions when we can make
a record in three dimensions.

> origin3D = #z .== 0.0 .+ origin

Once again, the type is inferred for us, and the record is exactly as expected.

In fact, we can do this generally.  The following function takes a name and a
record and adds the "name" field to that record with the given name.

> named :: a -> Rec r -> Rec ("name" .== a .+ r)
> named s r = #name .== s .+ r

Note that we require that the record we are naming must not have a "name" field
already.  Overlapping labels within a single record/variant is strictly forbidden.

Let's say we want to get the values out of the record.  Simple selection is achieved
with the .! operator, like so:

λ> origin .! #x
0.0

and we can use this to write whatever we want.  Here is a function for calculating
Euclidean distance from the origin to a point:

> distance :: (Floating t, r .! "y" ≈ t, r .! "x" ≈ t) => Rec r -> t
> distance p = sqrt $ p .! #x * p .! #x + p .! #y * p .! #y

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

> move :: (Num (r .! "x"), Num (r .! "y"))
>      => Rec r -> r .! "x" -> r .! "y" -> Rec r
> move p dx dy = Rec.update #x (p .! #x + dx) $
>                Rec.update #y (p .! #y + dy) p

Here, we're using the Rec.update operator to update the value at the label x by
adding dx to it, and then we do the same for y.
We can see it work in practice:

λ> move origin 3 4
 #x .== 3.0 .+ #y .== 4.0
λ> distance (move origin 3 4)
5.0
λ> distance (move (named "2D" origin3D) 5 12)
13.0

Note that if we were using row-types-lens and the lens library, we could write
move as:

move p dx dy = p & #x +~ dx & #y +~ dy

So far, we created an origin point in 2d and then one in 3d, but what if we are
adventurous mathematicians who want to have points in a space with some arbitrary
number of dimensions.  We could write out each of the 0s necessary, but there's
an easier way to initialize a record:

> origin4 :: Rec ("x" .== Double .+ "y" .== Double .+ "z" .== Double .+ "w" .== Double)
> origin4 = Rec.default' @Num 0

Finally, we have come to a case where GHC cannot infer the type signature, and how
could it!  The type is providing crucial information about the shape of the record.
Regardless, with the type provided, it works exactly as expected:

λ> origin4
 #w .== 0.0 .+ #x .== 0.0 .+ #y .== 0.0 .+ #z .== 0.0

While we have added names or further fields, we can also choose to forget
information in a record.  To remove a particular label, one can use the .-
operator, like so:

> unName :: HasType "name" a r => Rec r -> Rec (r .- "name")
> unName r = r .- #name

For larger changes, it is easier to use the restrict function.  The following
function will take a record that contains both an x and y coordinate and remove
the rest of the fields from it.

> get2D :: (r ≈ "x" .== Double .+ "y" .== Double, Disjoint r rest)
>       => Rec (r .+ rest)
>       -> Rec r
> get2D r = Rec.restrict r

GHC is a little finicky about the type operators and constraints -- indeed, some
slight modifications to the signature can easily cause type checking to fail.
However, a type signature is not necessary when
using type applications, and the function can instead be written as:

> get2D' r = Rec.restrict @("x" .== Double .+ "y" .== Double) r

with no trouble.  Yet another altnerative is to match directly on the values desired
using the :== and :+ record patterns:

> get2D'' :: (r ≈ "x" .== Double .+ "y" .== Double, Disjoint r rest)
>         => Rec (r .+ rest)
>         -> Rec r
> get2D'' ((Label :: Label "x") :== n1 :+ (Label :: Label "y") :== n2 :+ _)
>           = #x .== n1 .+ #y .== n2

(Note that overloaded labels cannot be used in the patterns, so the notation is
unfortunately bloated by types.  Also, the type operators are left associated,
so the "_" must go on the right, and the type signature is unforunately necessary.)

All three of the get2D functions behave the same.

--------------------------------------------------------------------------------
  VARIANTS
--------------------------------------------------------------------------------
Let's move on from records to variants.  In many ways, variants are quite similar,
as might be expected given that variants are dual to records.  The types look
almost the same, and some of the operators are shared as well.  However,
construction and destruction are obviously different.

Creating a variant can be done with IsJust:

> v,v' :: Var ("y" .== String .+ "x" .== Integer)
> v  = IsJust #x 1
> v' = IsJust #y "Foo"

Here, the type is necessary to specify what concrete type the variant is (when
using AllowAmbiguousTypes, the type is not always needed, but it would be needed
to e.g. show the variant).  In the simple case of a variant of just one type,
the simpler singleton function can be used:

> v2 = Var.singleton #x 1

Now, the type can be easily derived by GHC.  We can show variants as easily as
records:

λ> v
{x=1}
λ> v'
{y="Foo"}
λ> v2
{x=1}

Once created, a variant can be expanded by using type applications and the
diversify function.

> v3 = diversify @("y" .== String) v2
> v4 = diversify @("y" .== String .+ "z" .== Double) v2

λ> :t v4
v4 :: Var ('R '["x" ':-> Integer, "y" ':-> String, "z" ':-> Double])
λ> v == v3
True

The diversify function makes use of the .\/ type class, pronounced min-join.
The min-join of two row-types is the minimum row-type that contains all the
bindings of the two constituent ones.  This allows use to write a function to
join two lists of variants:

> joinVarLists :: forall x y. (WellBehaved (x .\/ y), x .\/ y ≈ y .\/ x)
>              => [Var x] -> [Var y] -> [Var (x .\/ y)]
> joinVarLists xs ys = map (diversify @y) xs ++ map (diversify @x) ys

Unfortunately, GHC cannot deduce that the min-join of x and y is the same as the
min-join of y and x, so  we must add that to the constraints.  However, any concrete
types x and y that we construct will have this property, so it is easy to dispatch
when we go to use this function.

Taking a step back, it's worth looking closer at the equality tests we did earlier
on variants.  Indeed, one may ask how equality works on variants at all.
For instance, v2 and v3 both look the same when you show them, and they
both have the same value inside, but can we test them for equality?  Indeed, we can't,
precisely because their types are different: it is a type error to even try to
check whether they're equal:

λ> v2 == v3
error:
    • Couldn't match type ‘'["y" ':-> [Char]]’ with ‘'[]’
      Expected type: Var ('R '["x" ':-> Integer])
        Actual type: Var ('R '["x" ':-> Integer] .+ ("y" .== String))
    • In the second argument of ‘(==)’, namely ‘v3’
      In the expression: v2 == v3
      In an equation for ‘it’: it = v2 == v3

This may look a little scary, but it's actually a pretty useful message.  Essentially,
it's expecting a variant that can only be an Integer at label "x", but it found one
that could also be a String at label "y".  So, comparing v2 and v3 is not allowed,
but since v3 now has the same labels as v1, that comparison is fine:

λ> v == v3
True
λ> v == IsJust #x 3
False
λ> v == v'
False
λ> v == IsJust #y "fail"
False

(Also note here that using IsJust without a type signature is fine because the correct
type can be easily inferred due to v's type.)

What can you do with a variant?  The only way to really use one is to get the value
out, and to do that, you must trial it:

λ> trial v #x
Left 1
λ> trial v #y
Right {x=1}
λ> trial v' #x
Right {y="Foo"}
λ> trial v' #y
Left "Foo"

If trialing at a label l succeeds, then it provides a Left value of the value at l.
If not, it provides a Right value of the variant with this label removed---since the
trial failed, we now can be sure that the value is not from l.

For ease of use in view patterns, Variants also exposes the view function.
(If using lens, this can be replaced with preview.)  With it, we can write a
function like this:

> myShow :: (r .! "y" ≈ String, Show (r .! "x")) => Var r -> String
> myShow (Var.view #x -> Just n) = "Showable of "++show n
> myShow (Var.view #y -> Just s) = "String of "++s
> myShow _ = "Unknown"

λ> myShow v
"Showable of 1"
λ> myShow v'
"String of Foo"
λ> myShow (just #z 3 :: Var ("y" .== String .+ "x" .== Integer .+ "z" .== Double))
"Unknown"

This can also be achieved with the IsJust pattern synonym in much the same way:

> myShow' :: (WellBehaved r, r .! "y" ≈ String, Show (r .! "x")) => Var r -> String
> myShow' (IsJust (Label :: Label "x") n) = "Showable of "++show n
> myShow' (IsJust (Label :: Label "y") s) = "String of "++s
> myShow' _ = "Unknown"

In either case, the type signature is once again totally derivable.

There are two minor annoyances with this.  First, it's fairly common to want to define
a function like myShow to be exhaustive in the variant's cases, but to do this,
you must manually provide a type signature:

> myShowRestricted :: Var ("y" .== String .+ "x" .== Integer) -> String
> myShowRestricted (Var.view #x -> Just n) = "Integer of "++show n
> myShowRestricted (Var.view #y -> Just s) = "String of "++s
> myShowRestricted _ = error "Unreachable"

The second blemish can be seen in this restricted version of myShow.  Even though
we know from the type that we've covered all the posibilities of the variant, GHC
will generate a "non-exhaustive pattern match" warning without the final line.
(This is true for the pattern synonym version too.)

One way to avoid this problem is to use switch.  The switch operator takes a variant
and a record such that for each label that the variant has, the record has a function
at that label that consumes the value the variant has and produces a value in a
common type.  Essentially, switch "applies" the variant to the record to produce
an output value.

> --myShowRestricted' :: Var ("y" .== String .+ "x" .== Integer) -> String
> myShowRestricted' v = switch v $
>      #x .== (\n -> "Integer of "++show n)
>   .+ #y .== (\s -> "String of "++s)

This version of myShow needs neither a type signature (it is inferred exactly) nor
a default "unreachable" case.  However, we no longer have the benefit of Haskell's
standard pattern matching.



A more powerful version of trial is multiTrial, which tests for multiple labels
at once.  With this, you can wholesale change the type of the variant to any (valid)
variant type you would like.  Of course, there needs to be a recourse if the variant
you provide is not expressible in the type you want, so multiTrial returns an Either
of the type you want or a Variant of the leftovers.  Consider the examples:

λ> :t multiTrial @("x" .== Double .+ "y" .== String) v
multiTrial @("x" .== Double .+ "y" .== String) v
  :: Either
       (Var ('R '["x" ':-> Double, "y" ':-> String]))
       (Var ('R '["x" ':-> Integer]))
λ> multiTrial @("x" .== Double .+ "y" .== String) v
Right {x=1}

λ> :t multiTrial @("x" .== Double .+ "y" .== String) v'
multiTrial @("x" .== Double .+ "y" .== String) v'
  :: Either
       (Var ('R '["x" ':-> Double, "y" ':-> String]))
       (Var ('R '["x" ':-> Integer]))
λ> multiTrial @("x" .== Double .+ "y" .== String) v'
Left {y="Foo"}

Thus, multiTrial can be used not only to arbitrarily split apart a variant, but
also to change unused label associations (in this case, we changed the variant
from one where "x" is an Integer to one where it's a Double).  We can even use
it to combine dispatching of two different variants at once:

> also :: Disjoint xs ys
>      => (Var xs -> a)
>      -> (Var ys -> a)
>      -> Var (xs .+ ys) -> a
> also f1 f2 e = case multiTrial e of
>   Left  e' -> f1 e'
>   Right e' -> f2 e'

The above also function takes two functions f1 and f2 that can each independently
be used on variants with rows xs and ys respectively.  Using multiTrial, we can
split the input variant (which is the join of xs and ys) and easily apply f1 or
f2 as appropriate.
