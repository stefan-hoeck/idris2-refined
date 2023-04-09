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

public export
hdec0All : HDec0 a p => (vs : List a) -> Maybe0 (All p vs)
hdec0All (x :: xs) = case hdec0 {p} x of
  Just0 v  => map (v::) $ hdec0All xs
  Nothing0 => Nothing0
hdec0All [] = Just0 []

public export %inline
HDec0 a p => HDec0 (List a) (All p) where hdec0 = hdec0All

public export
hdec0Any : HDec0 a p => (vs : List a) -> Maybe0 (Any p vs)
hdec0Any (x :: xs) = case hdec0 {p} x of
  Just0 v  => Just0 $ Here v
  Nothing0 => map There $ hdec0Any xs
hdec0Any [] = Nothing0

public export %inline
HDec0 a p => HDec0 (List a) (Any p) where hdec0 = hdec0Any

--------------------------------------------------------------------------------
--          HDec
--------------------------------------------------------------------------------

||| Hemi-decidability for non-erased predicates
public export
interface HDec (0 a : Type) (0 p : a -> Type) | p where
  hdec : (v : a) -> Maybe (p v)

public export
hdecAll : HDec a p => (vs : List a) -> Maybe (All p vs)
hdecAll (x :: xs) = case hdec {p} x of
  Just v  => map (v::) $ hdecAll xs
  Nothing => Nothing
hdecAll [] = Just []

public export %inline
HDec a p => HDec (List a) (All p) where hdec = hdecAll
