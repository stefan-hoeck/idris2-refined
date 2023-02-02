module Data.Refined

import public Data.List
import public Data.Maybe0
import public Data.Nat
import public Decidable.HDec

%default total

--------------------------------------------------------------------------------
--          Holds
--------------------------------------------------------------------------------

||| Proof that an (explicitly given) boolean predicate holds
public export
data Holds : (f : a -> Bool) -> a -> Type where
  ItHolds :
       {0 f : a -> Bool}
    -> {0 v : a}
    -> (prf : f v === True)
    -> Holds f v

public export
test : (b : Bool) -> Maybe0 (b === True)
test False = Nothing0
test True  = Just0 Refl

public export %inline
{f : a -> Bool} -> HDec0 a (Holds f) where
  hdec0 v = map (\v => ItHolds v) $ test (f v)

public export %inline
{f : a -> Bool} -> HDec a (Holds f) where
  hdec v with (f v) proof eq
    _ | True  = Just (ItHolds eq)
    _ | False = Nothing

--------------------------------------------------------------------------------
--          Conjunction and Disjunction
--------------------------------------------------------------------------------

||| Conjunction of two predicates
public export
data (&&) : (p : a -> Type) -> (q : a -> Type) -> a -> Type where
  And : {0 p,q : a -> Type} -> {0 v : a} -> p v -> q v -> (&&) p q v

public export %inline
HDec0 a p => HDec0 a q => HDec0 a (p && q) where
  hdec0 v = zipWith And (hdec0 v) (hdec0 v)

public export %inline
HDec a p => HDec a q => HDec a (p && q) where
  hdec v = [| And (hdec v) (hdec v) |]

||| Disjunction of two predicates
public export
data (||) : (p : a -> Type) -> (q : a -> Type) -> a -> Type where
  L : {0 p,q : a -> Type} -> {0 v : a} -> p v -> (||) p q v
  R : {0 p,q : a -> Type} -> {0 v : a} -> q v -> (||) p q v

public export %inline
HDec0 a p => HDec0 a q => HDec0 a (p || q) where
  hdec0 v = map L (hdec0 v) <|> map R (hdec0 v)

public export %inline
HDec a p => HDec a q => HDec a (p || q) where
  hdec v = map L (hdec v) <|> map R (hdec v)

--------------------------------------------------------------------------------
--          Natural Numbers
--------------------------------------------------------------------------------

public export
fromLTE : (k,v : Nat) -> {auto 0 prf : (k <= v) === True} -> LTE k v
fromLTE 0     _     = LTEZero
fromLTE (S k) (S j) = LTESucc (fromLTE k j)
fromLTE (S k) 0 impossible

public export %inline
{n : Nat} -> HDec0 Nat (LTE n) where
  hdec0 v with (n <= v) proof eq
    _ | True  = Just0 (fromLTE n v)
    _ | False = Nothing0

public export %inline
{n : Nat} -> HDec Nat (LTE n) where
  hdec v with (n <= v) proof eq
    _ | True  = Just (fromLTE n v)
    _ | False = Nothing

public export %inline
{n : Nat} -> HDec0 Nat (`LTE` n) where
  hdec0 v with (v <= n) proof eq
    _ | True  = Just0 (fromLTE v n)
    _ | False = Nothing0

public export %inline
{n : Nat} -> HDec Nat (`LTE` n) where
  hdec v with (v <= n) proof eq
    _ | True  = Just (fromLTE v n)
    _ | False = Nothing

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

public export
data Len : (p : Nat -> Type) -> List a -> Type where
  IsLen : {0 p : Nat -> Type} -> {0 s : List a} -> p (length s) -> Len p n

public export %inline
HDec0 Nat p => HDec0 (List a) (Len p) where
  hdec0 v = map IsLen $ hdec0 (length v)

public export %inline
HDec Nat p => HDec (List a) (Len p) where
  hdec v = map IsLen $ hdec (length v)

public export %inline
HDec0 (List a) NonEmpty where
  hdec0 (_ :: _) = Just0 %search
  hdec0 []       = Nothing0

public export %inline
HDec (List a) NonEmpty where
  hdec (_ :: _) = Just %search
  hdec []       = Nothing

--------------------------------------------------------------------------------
--          Integers
--------------------------------------------------------------------------------

public export
data Abs : (p : Nat -> Type) -> Integer -> Type where
  IsAbs : {0 p : Nat -> Type} -> {0 n : Integer} -> p (cast $ abs n) -> Abs p n

public export %inline
HDec0 Nat p => HDec0 Integer (Abs p) where
  hdec0 v = map IsAbs $ hdec0 (cast $ abs v)

public export %inline
HDec Nat p => HDec Integer (Abs p) where
  hdec v = map IsAbs $ hdec (cast $ abs v)

--------------------------------------------------------------------------------
--          Strings
--------------------------------------------------------------------------------

public export
data Str : (p : List Char -> Type) -> String -> Type where
  IsStr : {0 p : List Char -> Type} -> {0 s : String} -> p (unpack s) -> Str p n

public export %inline
HDec0 (List Char) p => HDec0 String (Str p) where
  hdec0 v = map IsStr $ hdec0 (unpack v)

public export %inline
HDec (List Char) p => HDec String (Str p) where
  hdec v = map IsStr $ hdec (unpack v)

||| Proof that a (non-empty) list of characters does not start with
||| a whitespace character.
public export
data LeftTrimmed : List Char -> Type where
  LTCons :
       {0 cs : _}
    -> {0 c : _}
    -> Holds (Prelude.not . Prelude.isControl) c
    -> LeftTrimmed (c :: cs)

public export %inline
HDec0 (List Char) LeftTrimmed where
  hdec0 (c::_)  = map LTCons $ hdec0 c
  hdec0 []      = Nothing0

public export %inline
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

public export %inline
HDec0 (List Char) RightTrimmed where
  hdec0 [c]     = map RT1 $ hdec0 c
  hdec0 (c::cs) = map RTCons $ hdec0 cs
  hdec0 []      = Nothing0

public export %inline
HDec (List Char) RightTrimmed where
  hdec [c]     = map RT1 $ hdec c
  hdec (c::cs) = map RTCons $ hdec cs
  hdec []      = Nothing

public export
0 Trimmed : List Char -> Type
Trimmed = LeftTrimmed && RightTrimmed
