module Decidable.HDec.Integer

import Data.Refined
import public Data.Prim.Integer
import public Decidable.HDec

public export %inline
{x : Integer} -> HDec0 Integer (< x) where
  hdec0 v = lt v x

public export %inline
{x : Integer} -> HDec0 Integer (x <) where
  hdec0 v = lt x v

public export %inline
{x : Integer} -> HDec0 Integer (<= x) where
  hdec0 v = lte v x

public export %inline
{x : Integer} -> HDec0 Integer (x <=) where
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
0 LessThan : Integer -> Integer -> Type
LessThan m n = n < m

||| `From m n` is an alias for `n <= m`.
public export
0 To : Integer -> Integer -> Type
To m n = ReflexiveClosure (<) n m

||| `GreaterThan m n` is an alias for `m < n`.
|||
||| This is useful when defining ranges such as
||| `From 2 && LessThan 10`, but it gives the wrong idea when used in
||| infix notation. So, don't do this: ```x `GreaterThan` 10```.
public export
0 GreaterThan : Integer -> Integer -> Type
GreaterThan = (<)

||| `From m n` is an alias for `m <= n`.
public export
0 From : Integer -> Integer -> Type
From = ReflexiveClosure (<)

||| `FromTo m n` is an alias for `From m && To n`.
public export
0 FromTo : Integer -> Integer -> Integer -> Type
FromTo m n = From m && To n

||| `Between m n` is an alias for `GreaterThan m && LessThan n`.
public export
0 Between : Integer -> Integer -> Integer -> Type
Between m n = GreaterThan m && LessThan n
