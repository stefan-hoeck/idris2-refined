module Main

import Decidable.HDec.Bits32
import Decidable.HDec.Int8
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
0 IsAlias : String -> Type
IsAlias = Str $ Trimmed && Len (`LTE` 50) && All (Holds IsPrintableASCII)

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
