module Decidable.HDec

import public Data.List.Quantifiers
import public Data.Maybe0

%default total

--------------------------------------------------------------------------------
--          HDec0
--------------------------------------------------------------------------------

||| Hemi-decidability for erased predicates
public export
interface HDec0 (0 a : Type) (0 p : a -> Type) | p where
  hdec0 : (v : a) -> Maybe0 (p v)

public export %inline
HDec0 a p => HDec0 (List a) (All p) where
  hdec0 []        = Just0 []
  hdec0 (x :: xs) = case hdec0 {p} x of
    Just0 v  => map (v::) $ hdec0 {p = All p} xs
    Nothing0 => Nothing0

--------------------------------------------------------------------------------
--          HDec
--------------------------------------------------------------------------------

||| Hemi-decidability for non-erased predicates
public export
interface HDec (0 a : Type) (0 p : a -> Type) | p where
  hdec : (v : a) -> Maybe (p v)
