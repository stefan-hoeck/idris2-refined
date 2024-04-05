module Main

import Control.Relation
import Control.Relation.ReflexiveClosure
import Data.Refined.Bits32
import Data.Refined.Int8
import Data.Refined.String
import Derive.Refined.JSON

%default total
%language ElabReflection

public export
record Percent where
  constructor MkPercent
  value : Bits32
  {auto 0 valid : value <= 100}

namespace Percent
  %runElab derive "Percent" [Show, Eq, Ord, RefinedInteger, RefinedJSON]

public export
IsPrintableASCII : Char -> Bool
IsPrintableASCII c = not (isControl c) && c <= '~'

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
  {auto 0 valid : IsAlias value}

namespace Alias
  %runElab derive "Alias" [Show, Eq, Ord, RefinedString, RefinedJSON]

public export
record Charge where
  constructor MkCharge
  value : Int8
  {auto 0 valid : FromTo (-8) 8 value}

namespace Charge
  %runElab derive "Charge" [Show, Eq, Ord, RefinedInteger, RefinedJSON]

main : IO ()
main = putStrLn "All tests passed"
