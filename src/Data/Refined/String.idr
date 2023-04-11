module Data.Refined.String

import public Data.Refined.Char
import public Data.Refined.List
import public Data.Refined.Core

%default total

public export
0 Len : (p : Integer -> Type) -> String -> Type
Len p = p `On` cast . prim__strLength

public export
0 Str : (p : List Char -> Type) -> String -> Type
Str p = p `On` unpack

||| Proof that a (non-empty) list of characters does not start with
||| a whitespace character.
public export
data LeftTrimmed : List Char -> Type where
  LTCons :
       {0 cs : _}
    -> {0 c : _}
    -> Holds (Prelude.not . Prelude.isControl) c
    -> LeftTrimmed (c :: cs)

public export
HDec0 (List Char) LeftTrimmed where
  hdec0 (c::_)  = map LTCons $ hdec0 c
  hdec0 []      = Nothing0

public export
HDec (List Char) LeftTrimmed where
  hdec (c::_)  = map LTCons $ hdec c
  hdec []      = Nothing

||| Proof that a list of characters does not start with a whitespace character.
public export
data RightTrimmed : List Char -> Type where
  RT1 :
       {0 c : _}
    -> Holds (Prelude.not . Prelude.isControl) c
    -> RightTrimmed [c]
  RTCons :
       {0 cs : _}
    -> {0 c : _}
    -> RightTrimmed cs
    -> RightTrimmed (c :: cs)

public export
HDec0 (List Char) RightTrimmed where
  hdec0 [c]     = map RT1 $ hdec0 c
  hdec0 (c::cs) = map RTCons $ hdec0 cs
  hdec0 []      = Nothing0

public export
HDec (List Char) RightTrimmed where
  hdec [c]     = map RT1 $ hdec c
  hdec (c::cs) = map RTCons $ hdec cs
  hdec []      = Nothing

public export
0 Trimmed : List Char -> Type
Trimmed = LeftTrimmed && RightTrimmed
