module Data.Refined.List

import public Data.List
import public Data.List.Quantifiers
import public Data.Refined.Core

%default total

public export
0 Len : (p : Nat -> Type) -> List a -> Type
Len p =  p `On` length

public export
HDec0 (List a) NonEmpty where
  hdec0 (_ :: _) = Just0 %search
  hdec0 []       = Nothing0

public export %inline
HDec (List a) NonEmpty where
  hdec (_ :: _) = Just %search
  hdec []       = Nothing
