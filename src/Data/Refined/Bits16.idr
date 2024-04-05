module Data.Refined.Bits16

import Control.Relation.ReflexiveClosure
import Control.Relation
import public Data.Prim.Bits16
import public Data.Refined.Core

%default total

public export %inline
{x : Bits16} -> HDec0 Bits16 (< x) where
  hdec0 v = lt v x

public export %inline
{x : Bits16} -> HDec0 Bits16 (x <) where
  hdec0 v = lt x v

public export %inline
{x : Bits16} -> HDec0 Bits16 (<= x) where
  hdec0 v = lte v x

public export %inline
{x : Bits16} -> HDec0 Bits16 (x <=) where
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
0 LessThan : Bits16 -> Bits16 -> Type
LessThan m n = n < m

||| `From m n` is an alias for `n <= m`.
public export
0 To : Bits16 -> Bits16 -> Type
To m n = ReflexiveClosure (<) n m

||| `GreaterThan m n` is an alias for `m < n`.
|||
||| This is useful when defining ranges such as
||| `From 2 && LessThan 10`, but it gives the wrong idea when used in
||| infix notation. So, don't do this: ```x `GreaterThan` 10```.
public export
0 GreaterThan : Bits16 -> Bits16 -> Type
GreaterThan = (<)

||| `From m n` is an alias for `m <= n`.
public export
0 From : Bits16 -> Bits16 -> Type
From = ReflexiveClosure (<)

||| `FromTo m n` is an alias for `From m && To n`.
public export
0 FromTo : Bits16 -> Bits16 -> Bits16 -> Type
FromTo m n = From m && To n

||| `Between m n` is an alias for `GreaterThan m && LessThan n`.
public export
0 Between : Bits16 -> Bits16 -> Bits16 -> Type
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
