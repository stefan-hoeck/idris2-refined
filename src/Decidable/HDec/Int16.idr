module Decidable.HDec.Int16

import Data.Refined
import public Data.Prim.Int16
import public Decidable.HDec

public export %inline
{x : Int16} -> HDec0 Int16 (< x) where
  hdec0 v = lt v x

public export %inline
{x : Int16} -> HDec0 Int16 (x <) where
  hdec0 v = lt x v

public export %inline
{x : Int16} -> HDec0 Int16 (<= x) where
  hdec0 v = lte v x

public export %inline
{x : Int16} -> HDec0 Int16 (x <=) where
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
0 LessThan : Int16 -> Int16 -> Type
LessThan m n = n < m

||| `From m n` is an alias for `n <= m`.
public export
0 To : Int16 -> Int16 -> Type
To m n = ReflexiveClosure (<) n m

||| `GreaterThan m n` is an alias for `m < n`.
|||
||| This is useful when defining ranges such as
||| `From 2 && LessThan 10`, but it gives the wrong idea when used in
||| infix notation. So, don't do this: ```x `GreaterThan` 10```.
public export
0 GreaterThan : Int16 -> Int16 -> Type
GreaterThan = (<)

||| `From m n` is an alias for `m <= n`.
public export
0 From : Int16 -> Int16 -> Type
From = ReflexiveClosure (<)

||| `FromTo m n` is an alias for `From m && To n`.
public export
0 FromTo : Int16 -> Int16 -> Int16 -> Type
FromTo m n = From m && To n

||| `Between m n` is an alias for `GreaterThan m && LessThan n`.
public export
0 Between : Int16 -> Int16 -> Int16 -> Type
Between m n = GreaterThan m && LessThan n
