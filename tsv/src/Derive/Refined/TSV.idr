module Derive.Refined.TSV

import public Derive.Refined
import public Derive.TSV
import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          TSVEncoder
--------------------------------------------------------------------------------

export
refinedEncDef : (fun : Name) -> (p : ParamTypeInfo) -> RefinedInfo p -> Decl
refinedEncDef fun (MkParamTypeInfo _ _ _ [c] _) (RI x) =
  def fun [patClause `(~(var fun) sc) `(encodeOnto sc . ~(var $ valName c.args x))]

||| Generate declarations and implementations for
||| `FromJSON` for a given refinement type.
export
RefinedTSVEncoderVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
RefinedTSVEncoderVis vis ns p = map decls $ refinedInfo p

  where
    decls : RefinedInfo p -> List TopLevel
    decls ri =
      let fun  := funName p "encodeOnto"
          impl := implName p "TSVEncoder"
       in [ TL (encClaim vis fun p) (refinedEncDef fun p ri)
          , TL (encoderImplClaim vis impl p) (encoderImplDef fun impl)
          ]

||| Generate declarations and implementations for
||| `FromJSON` for a given refinement type.
export %inline
RefinedTSVEncoder : List Name -> ParamTypeInfo -> Res (List TopLevel)
RefinedTSVEncoder = RefinedTSVEncoderVis Export

--------------------------------------------------------------------------------
--          TSVDecoder
--------------------------------------------------------------------------------

export
refinedDecDef : (fun, refineName : Name) -> Decl
refinedDecDef fun rn =
  def fun [patClause (var fun) `(refine decodeFrom ~(var rn))]

||| Generate declarations and implementations for
||| `TSVDecoder` for a given refinement type.
export
RefinedTSVDecoderVis :
     Visibility
  -> List Name
  -> ParamTypeInfo
  -> Res (List TopLevel)
RefinedTSVDecoderVis vis ns p = map decls $ refinedInfo p

  where
    decls : RefinedInfo p -> List TopLevel
    decls _ =
      let fun  := funName p "decodeFrom"
          impl := implName p "TSVDecoder"
          refn := refineName p
       in [ TL (decClaim vis fun p) (refinedDecDef fun refn)
          , TL (decoderImplClaim vis impl p) (decoderImplDef fun impl)
          ]

||| Generate declarations and implementations for
||| `TSVDecoder` for a given refinement type.
export %inline
RefinedTSVDecoder : List Name -> ParamTypeInfo -> Res (List TopLevel)
RefinedTSVDecoder = RefinedTSVDecoderVis Export

--------------------------------------------------------------------------------
--          TSV
--------------------------------------------------------------------------------

||| Generate declarations and implementations for
||| `TSVDecoder` and `TSVEncoder` for a given refinement type.
export %inline
RefinedTSV : List Name -> ParamTypeInfo -> Res (List TopLevel)
RefinedTSV ns p = sequenceJoin [RefinedTSVEncoder ns p, RefinedTSVDecoder ns p]
