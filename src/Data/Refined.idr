module Data.Refined

import public Control.Relation
import public Control.Relation.ReflexiveClosure
import public Data.List
import public Data.Refined.List
import public Data.Refined.Nat
import public Data.Refined.Core
import public Decidable.HDecEq

%default total

public export %inline
{v : a} -> HDecEq a => HDec0 a (v ===) where
  hdec0 = hdecEq v

%inline refl : (0 p : a === b) -> a === b
refl Refl = Refl

public export %inline
{v : a} -> HDecEq a => HDec a (v ===) where
  hdec x = case hdecEq v x of
    Just0 rfl => Just $ refl rfl
    Nothing0  => Nothing
