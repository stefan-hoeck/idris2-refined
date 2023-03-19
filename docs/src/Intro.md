# Refinement Types in Idris2

A refinement type is a type paired with a predicate, which is
assumed to hold for all values of the refinement type.

```idris
module Intro

import Language.Reflection.Pretty
import Language.Reflection.Util
import Data.DPair
import Decidable.HDec.Int8
import Decidable.HDec.Bits32
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection
```

As an example, consider the subset of non-empty strings. There
are several ways we could encode this predicate, one of which
is the following:

```idris
0 NonEmptyString : String -> Type
NonEmptyString = Str NonEmpty
```

`NonEmpty` is a predicate on lists from module `Data.List`, and
`Str` is a data type, which turns a predicate on lists
of characters into a predicate on strings by applying the
initial predicate to the unpacked string.

Restricting - or *refining* -  the values of an existing
type is a common thing do to, for instance when taking one of them as the argument
of an otherwise partial function. Typical examples are preventing
division by zero or taking the head of an empty list but also
sanitizing strings from user input by disallowing certain characters
or restricting the length of the string. As an example,
here is a function for computing the mean of a list of
floating point numbers. The list must be non-empty, otherwise
we risk a division by zero error:

```idris
mean : (ds : List Double) -> {auto 0 prf : NonEmpty ds} -> Double
mean ds = sum ds / cast (length ds)
```

We can only invoke function `mean` with a list of doubles `ds`,
if we can provide a value of `NonEmpty ds`: A proof that `ds` is
indeed non-empty. If the list is known at compile time, Idris will
do this for us automatically:

```idris
meanTest : Double
meanTest = mean [1,2,3]
```

If, however, we want to invoke `mean` with a list, the length of which
is not statically known, we need to come up with the required proof
at runtime. In case of lists, this is trivial: We just pattern match
on the list in question:

```idris
anyMean : List Double -> Double
anyMean []          = 0
anyMean xs@(_ :: _) = mean xs
```
## Combinators for Predicates

Coming up with a value of the desired predicate is not always
as simple as shown above. This is, for instance, the case, when we
combine several predicates. Here is an example for a refinement on
strings representing login names (the combinators come from module
`Data.Refined`):

```idris
public export
IsPrintableASCII : Char -> Bool
IsPrintableASCII c = not (isControl c) && c <= '~'

public export
0 IsAlias : String -> Type
IsAlias = Str $ Trimmed && Len (`LTE` 50) && All (Holds IsPrintableASCII)
```

The string must only consist of printable ASCII characters, must be
at most 50 characters long, and must not start or end with a space
character. Feel free to have a look at `Data.Refined` to find out,
how these predicates are defined. For instance, `Trimmed` is not
a primitive predicate but an alias for `RightTrimmed && LeftTrimmed`,
both of which imply `NonEmpty`:

```idris
trimmedImpliesNonEmpty : Trimmed cs -> NonEmpty cs
trimmedImpliesNonEmpty (And lt rt) = case lt of
  LTCons _ => IsNonEmpty
```

Manually verifying that this predicate holds is tedious, so there are
two interfaces for helping us with this: `Decidable.HDec.HDec0`,
if we want to make sure that the proof value is not built up at
runtime (which is what we typically want when refining primitives)
and `HDec` for non-erased proofs. In both cases, the verifying
function does not return a `Dec` but only a `Maybe` or `Maybe0`
(for erased proofs). This makes deciding on this predicates not
as powerful as with full-fledged decidability, but makes the
deciding functions much simpler to implement. (`HDec` is
an abbreviation for *hemi-decidable*.)

Here's an example how to use `hdec0` in practice:

```idris
printAlias : (s : String) -> {auto 0 prf : IsAlias s} -> IO ()
printAlias s = putStrLn "Your alias is \"\{s}\""

runtimePrintAlias : String -> IO ()
runtimePrintAlias s = case hdec0 {p = IsAlias} s of
  Just0 _  => printAlias s
  Nothing0 => putStrLn "Not a valid alias: \{show s}"

main : IO ()
main = runtimePrintAlias "Stefan"
```

Unfortunately, the following does not work, even though the string
is known at compile time:


```idris
failing
  compileTimePrint : IO ()
  compileTimePrint = printAlias "Stefan"
```

The proof of validity Idris has to come up with in this case is just
too complex, so proof search aborts before finding a solution.
We will see in the next section, how this can be made more convenient
to use.

## Pairing Values with Proofs

So far, we have just refined the *arguments* of functions. However, we often
also want to refine the results of functions, in order not to have
to refine those values again later on. This is of course when we
return a dependent pair (for unerased proofs) or a `Data.DPair.Subset`
(for erased proofs):

```idris
alias : String -> Maybe (Subset String IsAlias)
alias s = case hdec0 {p = IsAlias} s of
  Just0 v  => Just $ Element s v
  Nothing0 => Nothing
```

However, most refinement types have also distinct semantics, in which
case it makes sense to wrap them up in a specific record type:

```idris
public export
record Alias where
  constructor MkAlias
  value : String
  {auto 0 prf : IsAlias value}

public export
refineAlias : String -> Maybe Alias
refineAlias s = case hdec0 {p = IsAlias} s of
  Just0 _  => Just $MkAlias s
  Nothing0 => Nothing
```

Even better, we can now get back our safe usage of string literals,
because now, the actual proof search can be drastically simplified:

```idris
public export
fromString : (s : String) -> {auto 0 prf : IsJust (refineAlias s)} -> Alias
fromString s = fromJust $ refineAlias s

stefan : Alias
stefan = "Stefan"
```

Since all of the above is pretty boring to write, the utilities for
refined primitives can be generated automatically by means of
elaborator reflection (we need to put this stuff in its own
namespace, because there is already a function called `fromString`
in this modules):

```idris
public export
record AutoAlias where
  constructor MkAutoAlias
  value : String
  {auto 0 prf : IsAlias value}

namespace AutoAlias
  %runElab derive "AutoAlias" [Show, Eq, RefinedString]

hoeck : AutoAlias
hoeck = "Stefan Hoeck"
```

## Refined Integers

Another use case that often comes up is the refinement of numeric types,
because only a subset of values might be acceptable as input for a
given function. For the integral primitives, there are predefined relations
(and hence, if they are being partially applied, predicates) in
the [idris2-algebra library](https://github.com/stefan-hoeck/idris2-algebra),
which come with associated laws.

Here is an example:

```idris
public export
record Percent where
  constructor MkPercent
  value : Bits32
  {auto 0 valid : value <= 100}

namespace Percent
  %runElab derive "Percent" [Show, Eq, Ord, RefinedInteger]
```

Here is another example for atom charges in a molecule:

```idris
public export
record Charge where
  constructor MkCharge
  value : Int8
  {auto 0 valid : FromTo (-8) 8 value}

namespace Charge
  %runElab derive "Charge" [Show, Eq, Ord, RefinedInteger]
```

```idris
public export
record Phantom (a : Type) where
  constructor MkPhantom
  value : String
  {auto 0 prf : IsAlias value}

namespace Phantom
  %runElab derive "Phantom" [Show, Eq, RefinedString]
```

## Conclusion

In Idris, working with refinement types should be pretty straight
forward, and the goal of this library is to provide the necessary
utilities for defining precise predicates and verifying that those
predicates hold.

<!-- vi: filetype=idris2:syntax=markdown
-->
