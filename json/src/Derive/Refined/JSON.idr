module Derive.Refined.JSON

import public Derive.Refined
import public JSON.Simple.Derive
import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          ToJSON
--------------------------------------------------------------------------------

export
refinedToJsonDef : (fun : Name) -> (p : ParamTypeInfo) -> RefinedInfo p -> Decl
refinedToJsonDef fun (MkParamTypeInfo _ _ _ [c] _) (RI x) =
  def fun [patClause (var fun) `(toJSON . ~(var $ valName c.args x))]

||| Generate declarations and implementations for
||| `FromJSON` for a given refinement type.
export %inline
RefinedToJSON : List Name -> ParamTypeInfo -> Res (List TopLevel)
RefinedToJSON ns p = map decls $ refinedInfo p

  where
    decls : RefinedInfo p -> List TopLevel
    decls ri =
      let fun  := funName p "toJson"
          impl := implName p "ToJSON"
       in [ TL (toJsonClaim fun p)
               (refinedToJsonDef fun p ri)
          , TL (toJsonImplClaim impl p) (toJsonImplDef fun impl)
            ]

--------------------------------------------------------------------------------
--          FromJSON
--------------------------------------------------------------------------------

public export
refineFromJSON : FromJSON a => String -> (a -> Maybe b) -> Parser JSON b
refineFromJSON str f v = case fromJSON v of
  Right va => case f va of
    Just vb => Right vb
    Nothing => fail "refining \{str} failed: \{show v}"
  Left s   => prependContext str $ Left s

export
refinedFromJsonDef : (fun,typeName, refineName : Name) -> Decl
refinedFromJsonDef fun tn rn =
  def fun [patClause (var fun) `(refineFromJSON ~(tn.namePrim) ~(var rn))]

||| Generate declarations and implementations for
||| `FromJSON` for a given refinement type.
export %inline
RefinedFromJSON : List Name -> ParamTypeInfo -> Res (List TopLevel)
RefinedFromJSON ns p = map decls $ refinedInfo p

  where
    decls : RefinedInfo p -> List TopLevel
    decls _ =
      let fun  := funName p "fromJson"
          impl := implName p "FromJSON"
          refn := refineName p
       in [ TL (fromJsonClaim fun p)
               (refinedFromJsonDef fun p.getName refn)
          , TL (fromJsonImplClaim impl p) (fromJsonImplDef fun impl)
            ]

--------------------------------------------------------------------------------
--          JSON
--------------------------------------------------------------------------------

||| Generate declarations and implementations for
||| `FromJSON` and `ToJSON` for a given refinement type.
export %inline
RefinedJSON : List Name -> ParamTypeInfo -> Res (List TopLevel)
RefinedJSON ns p = sequenceJoin [RefinedToJSON ns p, RefinedFromJSON ns p]
