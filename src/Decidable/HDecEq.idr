module Decidable.HDecEq

import public Data.List.Quantifiers
import public Data.Maybe0

%default total

||| Hemi-decidable equality.
public export
interface HDecEq a where
  hdecEq : (x,y : a) -> Maybe0 (x === y)

export
HDecEq Bits8 where
  hdecEq x y = case prim__eq_Bits8 x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Bits16 where
  hdecEq x y = case prim__eq_Bits16 x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Bits32 where
  hdecEq x y = case prim__eq_Bits32 x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Bits64 where
  hdecEq x y = case prim__eq_Bits64 x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Int8 where
  hdecEq x y = case prim__eq_Int8 x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Int16 where
  hdecEq x y = case prim__eq_Int16 x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Int32 where
  hdecEq x y = case prim__eq_Int32 x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Int64 where
  hdecEq x y = case prim__eq_Int64 x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Integer where
  hdecEq x y = case prim__eq_Integer x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Int where
  hdecEq x y = case prim__eq_Int x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq Char where
  hdecEq x y = case prim__eq_Char x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq String where
  hdecEq x y = case prim__eq_String x y of
    0 => Nothing0
    _ => Just0 (believe_me $ Refl {x})

export
HDecEq a => HDecEq (Maybe a) where
  hdecEq Nothing Nothing   = Just0 Refl
  hdecEq (Just x) (Just y) = map (cong Just) (hdecEq x y)
  hdecEq _        _        = Nothing0

export
HDecEq a => HDecEq b => HDecEq (Either a b) where
  hdecEq (Left x)  (Left y)  = map (cong Left) (hdecEq x y)
  hdecEq (Right x) (Right y) = map (cong Right) (hdecEq x y)
  hdecEq _        _          = Nothing0

export
HDecEq a => HDecEq b => HDecEq (Pair a b) where
  hdecEq (x1,y1) (x2,y2) = case hdecEq x1 x2 of
    Just0 r1 => case hdecEq y1 y2 of
      Just0 r2 => Just0 (cong2 MkPair r1 r2)
      Nothing0   => Nothing0
    Nothing0 => Nothing0

0 eqNatToEqual : (x,y : Nat) -> (x == y) === True -> x === y
eqNatToEqual 0 0         p = Refl
eqNatToEqual (S k) (S m) p = cong S $ eqNatToEqual k m p
eqNatToEqual 0     (S k) p impossible
eqNatToEqual (S k) 0     p impossible

hdecEqNat : (x,y : Nat) -> Maybe0 (x === y)
hdecEqNat x y with (x == y) proof eq
  _ | True  = Just0 (eqNatToEqual x y eq)
  _ | False = Nothing0

export %inline
HDecEq Nat where
  hdecEq = hdecEqNat

export
HDecEq a => HDecEq (List a) where
  hdecEq [] [] = Just0 Refl
  hdecEq (h1 :: t1) (h2 :: t2) = case hdecEq h1 h2 of
    Just0 r1 => case hdecEq t1 t2 of
      Just0 r2 => Just0 (cong2 (::) r1 r2)
      Nothing0   => Nothing0
    Nothing0 => Nothing0
  hdecEq _ _ = Nothing0

export
(prf : All (HDecEq . f) ks) => HDecEq (All f ks) where
  hdecEq [] [] = Just0 Refl
  hdecEq {prf = _ :: _} (h1 :: t1) (h2 :: t2) = case hdecEq h1 h2 of
    Just0 r1 => case hdecEq t1 t2 of
      Just0 r2 => Just0 (cong2 (::) r1 r2)
      Nothing0   => Nothing0
    Nothing0 => Nothing0
  hdecEq _ _ = Nothing0

export
(p : All (HDecEq . f) ks) => HDecEq (Any f ks) where
  hdecEq {p = _ :: _} (Here x)  (Here y)  = map (cong Here) $ hdecEq x y
  hdecEq {p = _ :: _} (There x) (There y) = map (cong There) $ hdecEq x y
  hdecEq _ _ = Nothing0
