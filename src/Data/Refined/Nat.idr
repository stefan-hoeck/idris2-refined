module Data.Refined.Nat

import public Data.Nat
import public Data.Refined.Core

%default total

public export
fromLTE : (k,v : Nat) -> {auto 0 prf : (k <= v) === True} -> LTE k v
fromLTE 0     _     = LTEZero
fromLTE (S k) (S j) = LTESucc (fromLTE k j)
fromLTE (S k) 0 impossible

public export
{n : Nat} -> HDec0 Nat (LTE n) where
  hdec0 v with (n <= v) proof eq
    _ | True  = Just0 (fromLTE n v)
    _ | False = Nothing0

public export
{n : Nat} -> HDec Nat (LTE n) where
  hdec v with (n <= v) proof eq
    _ | True  = Just (fromLTE n v)
    _ | False = Nothing

public export
{n : Nat} -> HDec0 Nat (`LTE` n) where
  hdec0 v with (v <= n) proof eq
    _ | True  = Just0 (fromLTE v n)
    _ | False = Nothing0

public export
{n : Nat} -> HDec Nat (`LTE` n) where
  hdec v with (v <= n) proof eq
    _ | True  = Just (fromLTE v n)
    _ | False = Nothing

public export
HDec0 Nat IsSucc where
  hdec0 0     = Nothing0
  hdec0 (S _) = Just0 %search
