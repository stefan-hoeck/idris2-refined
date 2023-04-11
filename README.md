# idris2-refined: Refinement types for Idris2

This library provides predicates, combinators, and elaborator
scripts for working with refinement types with a focus on
refined primitives. Here is a motivating example:

```idris
module README

import Data.Refined
import Data.Refined.String
import Data.Refined.Integer
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection

public export
MaxLen : Nat
MaxLen = 50

public export
0 IsAlias : String -> Type
IsAlias = Str $ Trimmed && Len (`LTE` MaxLen) && All PrintableAscii

public export
record Alias where
  constructor MkAlias
  value : String
  {auto 0 prf : IsAlias value}

%runElab derive "Alias" [Show, Eq, RefinedString]

hoeck : Alias
hoeck = "Stefan Hoeck"
```

Here's a link to a more [detailed introduction](docs/src/Intro.md)

## Prerequisites

This library uses [elab-util](https://github.com/stefan-hoeck/idris2-elab-util).
It is therefore recommended to use a package manager such as
[pack](https://github.com/stefan-hoeck/idris2-pack) for taking care
of your Idris dependencies.

<!-- vi: filetype=idris2:syntax=markdown
-->
