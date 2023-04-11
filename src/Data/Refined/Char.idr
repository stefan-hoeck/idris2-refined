module Data.Refined.Char

import public Data.Prim.Char
import public Data.Refined.Core

public export %inline
{x : Char} -> HDec0 Char (< x) where
  hdec0 v = lt v x

public export %inline
{x : Char} -> HDec0 Char (x <) where
  hdec0 v = lt x v

public export %inline
{x : Char} -> HDec0 Char (<= x) where
  hdec0 v = lte v x

public export %inline
{x : Char} -> HDec0 Char (x <=) where
  hdec0 v = lte x v

--------------------------------------------------------------------------------
--          Non-operators
--------------------------------------------------------------------------------

||| `LessThan m n` is an alias for `n < m`.
|||
||| This is useful when defining ranges such as
||| `From 2 && LessThan 10`, but it gives the wrong idea when used in
||| infix notation. So, don't do this: ```x `LessThan` 10```.
public export
0 LessThan : Char -> Char -> Type
LessThan m n = n < m

||| `From m n` is an alias for `n <= m`.
public export
0 To : Char -> Char -> Type
To m n = ReflexiveClosure (<) n m

||| `GreaterThan m n` is an alias for `m < n`.
|||
||| This is useful when defining ranges such as
||| `From 2 && LessThan 10`, but it gives the wrong idea when used in
||| infix notation. So, don't do this: ```x `GreaterThan` 10```.
public export
0 GreaterThan : Char -> Char -> Type
GreaterThan = (<)

||| `From m n` is an alias for `m <= n`.
public export
0 From : Char -> Char -> Type
From = ReflexiveClosure (<)

||| `FromTo m n` is an alias for `From m && To n`.
public export
0 FromTo : Char -> Char -> Char -> Type
FromTo m n = From m && To n

||| `Between m n` is an alias for `GreaterThan m && LessThan n`.
public export
0 Between : Char -> Char -> Char -> Type
Between m n = GreaterThan m && LessThan n

--------------------------------------------------------------------------------
--          Widenings
--------------------------------------------------------------------------------

export
0 widen :
     FromTo m n x
  -> {auto 0 p1 : m2 <= m}
  -> {auto 0 p2 : n  <= n2}
  -> FromTo m2 n2 x
widen (And y z) = And (transitive p1 y) (transitive z p2)

export
0 widen' :
     Between m n x
  -> {auto 0 p1 : m2 <= m}
  -> {auto 0 p2 : n  <= n2}
  -> Between m2 n2 x
widen' (And y z) = And (strictRight p1 y) (strictLeft z p2)

--------------------------------------------------------------------------------
--          Classes
--------------------------------------------------------------------------------

public export
0 Ascii : Char -> Type
Ascii = (< '\128')

public export
0 Printable : Char -> Type
Printable = Holds (not . isControl)

public export
0 PrintableAscii : Char -> Type
PrintableAscii = Ascii && Printable

public export
0 Upper : Char -> Type
Upper = FromTo 'A' 'Z'

public export
0 Lower : Char -> Type
Lower = FromTo 'a' 'z'

public export
0 Binit : Char -> Type
Binit = FromTo '0' '1'

public export
0 Octit : Char -> Type
Octit = FromTo '0' '9'

public export
0 Digit : Char -> Type
Digit = FromTo '0' '9'

public export
0 Hexit : Char -> Type
Hexit = Digit || FromTo 'a' 'f' || FromTo 'A' 'F'

public export
0 Alpha : Char -> Type
Alpha = Lower || Upper

public export
0 AlphaNum : Char -> Type
AlphaNum = Alpha || Digit
