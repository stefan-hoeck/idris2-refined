module Derive.HDecEq

import public Decidable.HDecEq
import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level declaration implementing the equality test for
||| the given data type.
export
hdeceqClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
hdeceqClaim vis fun p =
  let arg := var p.info.name
      tpe := `((x : ~(arg)) -> (y : ~(arg)) -> Maybe0 (x === y))
   in simpleClaim vis fun tpe

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
hdeceqImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
hdeceqImplClaim vis impl p = implClaimVis vis impl (implType "HDecEq" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

hdeceqImplDef : (fun, impl : Name) -> Decl
hdeceqImplDef fun impl =
  def impl [patClause (var impl) (var "MkHDecEq" `app` var fun)]

-- catch-all pattern clause for data types with more than
-- one data constructor
catchAll : (fun : Name) -> TypeInfo -> List Clause
catchAll fun ti =
  if length ti.cons > 1
     then [patClause `(~(var fun) _ _) `(Nothing0)]
     else []

||| Generates pattern match clauses for the constructors of
||| the given data type. `fun` is the name of the function we implement.
||| This is either a local function definition in case of a
||| custom derivation, or the name of a top-level function.
export
hdeceqClauses : (fun : Name) -> TypeInfo -> List Clause
hdeceqClauses fun ti = map clause ti.cons ++ catchAll fun ti

 where
   clause : Con ti.arty ti.args -> Clause
   clause c =
     let v := var c.name
      in patClause `(~(var fun) ~(v) ~(v)) `(Just0 Refl)

||| Definition of a (local or top-level) function implementing
||| the equality check for the given data type.
export
hdeceqDef : Name -> TypeInfo -> Decl
hdeceqDef fun ti = def fun (hdeceqClauses fun ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

export
failEnum : Res a
failEnum = Left "Interface HDecEq can currently only be derived for enumerations"

||| Generate declarations and implementations for `Eq` for a given data type.
export
HDecEqVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
HDecEqVis vis nms p = case isEnum p.info of
  True  =>
    let fun  := funName p "hdecEq"
        impl := implName p "HDecEq"
     in Right
          [ TL (hdeceqClaim vis fun p) (hdeceqDef fun p.info)
          , TL (hdeceqImplClaim vis impl p) (hdeceqImplDef fun impl)
          ]
  False => failEnum

||| Alias for `EqVis Public`
export %inline
HDecEq : List Name -> ParamTypeInfo -> Res (List TopLevel)
HDecEq = HDecEqVis Public
