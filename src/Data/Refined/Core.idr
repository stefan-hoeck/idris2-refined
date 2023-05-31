module Data.Refined.Core

import public Data.DPair
import public Data.Maybe0
import public Decidable.HDec

%default total

--------------------------------------------------------------------------------
--          Always and Never
--------------------------------------------------------------------------------

||| The predicate that always holds.
public export
data Always : a -> Type where
  Yes : Always a

public export %inline
HDec0 a Always where hdec0 _ = Just0 Yes

public export %inline
HDec a Always where hdec _ = Just Yes

||| The predicate that never holds.
public export
data Never : a -> Type where

public export %inline
HDec0 a Never where hdec0 _ = Nothing0

public export %inline
HDec a Never where hdec _ = Nothing

--------------------------------------------------------------------------------
--          Conjunction and Disjunction
--------------------------------------------------------------------------------

||| Conjunction of two predicates
public export
data (&&) : (p : a -> Type) -> (q : a -> Type) -> a -> Type where
  And : {0 p,q : a -> Type} -> {0 v : a} -> p v -> q v -> (&&) p q v

public export
mapFst : {0 p,q,r : _} -> (p x -> r x) -> (p && q) x -> (r && q) x
mapFst f (And v w) = And (f v) w

public export
mapSnd : {0 p,q,r : _} -> (q x -> r x) -> (p && q) x -> (p && r) x
mapSnd f (And v w) = And v (f w)

public export
HDec0 a p => HDec0 a q => HDec0 a (p && q) where
  hdec0 v = zipWith And (hdec0 v) (hdec0 v)

public export
HDec a p => HDec a q => HDec a (p && q) where
  hdec v = [| And (hdec v) (hdec v) |]

||| Disjunction of two predicates
public export
data (||) : (p : a -> Type) -> (q : a -> Type) -> a -> Type where
  L : {0 p,q : a -> Type} -> {0 v : a} -> p v -> (||) p q v
  R : {0 p,q : a -> Type} -> {0 v : a} -> q v -> (||) p q v

public export
mapL : {0 p,q,r : _} -> (p x -> r x) -> (p || q) x -> (r || q) x
mapL f (L v) = L $ f v
mapL f (R v) = R v

public export
mapR : {0 p,q,r : _} -> (q x -> r x) -> (p || q) x -> (p || r) x
mapR f (L v) = L v
mapR f (R v) = R $ f v

public export
HDec0 a p => HDec0 a q => HDec0 a (p || q) where
  hdec0 v = map L (hdec0 v) <|> map R (hdec0 v)

public export
HDec a p => HDec a q => HDec a (p || q) where
  hdec v = map L (hdec v) <|> map R (hdec v)

export
deMorgan1 : {0 p,q : a -> Type} -> Not ((p || q) v) -> (Not . p && Not . q) v
deMorgan1 f = And (f . L) (f . R)

--------------------------------------------------------------------------------
--          Non-operators
--------------------------------------------------------------------------------

||| `Equals m n` is an alias for `n === m`.
|||
||| This is useful when using the `(||)` operator, a disjunction of two
||| predicates.
||| For example, using `hdec0` you could write:
|||
||| ```idris example
||| hdec0 {p = (Equals 0 || Equals 15 || Equals 30)} value
||| ```
public export
0 Equals : a -> a -> Type
Equals = (===)

--------------------------------------------------------------------------------
--          On
--------------------------------------------------------------------------------

public export
data On : (a -> Type) -> (f : b -> a) -> b -> Type where
  HoldsOn :
       {0 p : a -> Type}
    -> {0 f : b -> a}
    -> {0 v : b}
    -> p (f v)
    -> On p f v

public export
{f : b -> a} -> HDec0 a p => HDec0 b (p `On` f) where
  hdec0 v = map HoldsOn $ hdec0 (f v)

public export
{f : b -> a} -> HDec a p => HDec b (p `On` f) where
  hdec v = map HoldsOn $ hdec (f v)

public export
mapOn : {0 p,q : _} -> (p (f x) -> q (f x)) -> On p f x -> On q f x
mapOn g (HoldsOn y) = HoldsOn $ g y

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

0 and : (b === True) -> (c === True) -> (b && c) === True
and Refl Refl = Refl

0 and' : {b,c : Bool} -> (b && c) === True -> (b === True, c === True)
and' {b = True, c = True}  prf = (Refl, Refl)
and' {b = True, c = False} prf = absurd prf
and' {b = False}           prf = absurd prf

||| Conversion from type-level `(&&)` to boolean `(&&)`
export
0 holdsAnd :
     {f,g : a -> Bool}
  -> (v : a)
  -> (Holds f && Holds g) v
  -> Holds (\x => f x && g x) v
holdsAnd v (And (ItHolds p1) (ItHolds p2)) = ItHolds (and p1 p2)

||| Conversion from boolean `(&&)` to type-level `(&&)`
export
0 andHolds :
     {f,g : a -> Bool}
  -> (v : a)
  -> Holds (\x => f x && g x) v
  -> (Holds f && Holds g) v
andHolds v (ItHolds prf) =
  let (x,y) := and' prf
   in And (ItHolds x) (ItHolds y)

0 or1 : (b === True) -> (b || c) === True
or1 Refl = Refl

0 or2 : (c === True) -> (b || c) === True
or2 {b = True}  Refl = Refl
or2 {b = False} Refl = Refl

0 or' : {b,c : Bool} -> (b || c) === True -> Either (b === True) (c === True)
or' {b = True}             p = Left Refl
or' {c = True}             p = Right Refl
or' {b = False, c = False} p = absurd p

||| Conversion from type-level `(||)` to boolean `(||)`
export
0 holdsOr :
     {f,g : a -> Bool}
  -> (v : a)
  -> (Holds f || Holds g) v
  -> Holds (\x => f x || g x) v
holdsOr v (L $ ItHolds p) = ItHolds (or1 p)
holdsOr v (R $ ItHolds p) = ItHolds (or2 p)

||| Conversion from boolean `(||)` to type-level `(||)`
export
0 orHolds :
     {f,g : a -> Bool}
  -> (v : a)
  -> Holds (\x => f x || g x) v
  -> (Holds f || Holds g) v
orHolds v (ItHolds p) = case or' p of
  Left  p' => L $ ItHolds p'
  Right p' => R $ ItHolds p'

--------------------------------------------------------------------------------
--          Const
--------------------------------------------------------------------------------

||| The `Const` predicate.
|||
||| This allows us to refine a value based on a refinement on a second
||| value.
public export
data Const : (p : e -> Type) -> (v : e) -> t -> Type where
  C : {0 p : e -> Type} -> p v -> Const p v x

public export
unConst : Const p v t -> p v
unConst (C prf) = prf

public export
{v : e} -> HDec0 e p => HDec0 t (Const p v) where
  hdec0 _ = map C $ hdec0 {p} v

--------------------------------------------------------------------------------
--          Refine
--------------------------------------------------------------------------------

||| Try to refine a value into a `Subset`.
public export
refine0 : HDec0 a p => a -> Maybe (Subset a p)
refine0 x = case hdec0 {p} x of
  Just0 prf => Just $ Element x prf
  Nothing0  => Nothing

||| Try to refine a value into a `DPair`.
public export
refine : HDec a p => a -> Maybe (DPair a p)
refine x = case hdec {p} x of
  Just prf => Just $ (x ** prf)
  Nothing  => Nothing
