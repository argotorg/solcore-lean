import Solcore.Core.Wire.V3.Codec.TypeProperties

/-! Data-definition and array codecs for Semantic Core Wire v3. -/

set_option autoImplicit false

namespace Solcore.Core.Wire.V3

def encodeTypeList (types : List Ty) : Lean.Json :=
  .arr (types.map encodeType).toArray

def decodeTypeListAtWithDepth
    (maxDepth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (List Ty) :=
  decodeArrayAt (decodeTypeAtWithDepth maxDepth) path json

def decodeTypeListWithDepth
    (maxDepth : Nat)
    (json : Lean.Json) :
    DecodeResult (List Ty) :=
  decodeTypeListAtWithDepth maxDepth .root json

def TypesFitDepth (maxDepth : Nat) (types : List Ty) : Prop :=
  ∀ type ∈ types, typeDepth type ≤ maxDepth

private theorem decodeTypeJsonListAt_encode
    (maxDepth : Nat)
    (types : List Ty)
    (path : DecodePath)
    (index : Nat)
    (fit : TypesFitDepth maxDepth types) :
    decodeListAt (decodeTypeAtWithDepth maxDepth) path index
      (types.map encodeType) = .ok types := by
  induction types generalizing index with
  | nil => rfl
  | cons head tail ih =>
      have headFit : typeDepth head ≤ maxDepth := fit head (by simp)
      have tailFit : TypesFitDepth maxDepth tail := by
        intro type member
        exact fit type (by simp [member])
      simp only [List.map_cons, decodeListAt]
      rw [decodeTypeAtWithDepth_encodeType head (path.index index) maxDepth headFit]
      rw [ih (index + 1) tailFit]
      rfl

theorem decodeTypeListAtWithDepth_encodeTypeList
    (maxDepth : Nat)
    (types : List Ty)
    (path : DecodePath)
    (fit : TypesFitDepth maxDepth types) :
    decodeTypeListAtWithDepth maxDepth path (encodeTypeList types) = .ok types := by
  simpa [decodeTypeListAtWithDepth, encodeTypeList, decodeArrayAt] using
    decodeTypeJsonListAt_encode maxDepth types path 0 fit

namespace DataDefinition

def FitsDepth (maxDepth : Nat) (definition : DataDefinition) : Prop :=
  TypesFitDepth maxDepth definition.constructorPayloadTypes

end DataDefinition

def encodeDataDefinition (definition : DataDefinition) : Lean.Json :=
  .mkObj [
    ("constructorPayloadTypes",
      encodeTypeList definition.constructorPayloadTypes)
  ]

def decodeDataDefinitionAtWithDepth
    (maxDepth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult DataDefinition := do
  ensureExactObject path json ["constructorPayloadTypes"]
    ["constructorPayloadTypes"]
  let payloadTypes ← decodeTypeListAtWithDepth maxDepth
    (path.field "constructorPayloadTypes")
    (← requireField path json "constructorPayloadTypes")
  pure { constructorPayloadTypes := payloadTypes }

def decodeDataDefinitionWithDepth
    (maxDepth : Nat)
    (json : Lean.Json) :
    DecodeResult DataDefinition :=
  decodeDataDefinitionAtWithDepth maxDepth .root json

theorem decodeDataDefinitionAtWithDepth_encodeDataDefinition
    (maxDepth : Nat)
    (definition : DataDefinition)
    (path : DecodePath)
    (fit : definition.FitsDepth maxDepth) :
    decodeDataDefinitionAtWithDepth maxDepth path
      (encodeDataDefinition definition) = .ok definition := by
  cases definition with
  | mk payloadTypes =>
      change (do
        let decodedPayloadTypes ← decodeTypeListAtWithDepth maxDepth
          (path.field "constructorPayloadTypes") (encodeTypeList payloadTypes)
        pure (DataDefinition.mk decodedPayloadTypes)) =
          .ok (DataDefinition.mk payloadTypes)
      rw [decodeTypeListAtWithDepth_encodeTypeList maxDepth payloadTypes
        (path.field "constructorPayloadTypes") fit]
      rfl

def encodeDataDefinitions (definitions : DataEnvironment) : Lean.Json :=
  .arr (definitions.map encodeDataDefinition).toArray

def decodeDataDefinitionsAtWithDepth
    (maxDepth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult DataEnvironment :=
  decodeArrayAt (decodeDataDefinitionAtWithDepth maxDepth) path json

def DataEnvironmentFitsDepth
    (maxDepth : Nat)
    (definitions : DataEnvironment) : Prop :=
  ∀ definition ∈ definitions, definition.FitsDepth maxDepth

private theorem decodeDefinitionJsonListAt_encode
    (maxDepth : Nat)
    (definitions : DataEnvironment)
    (path : DecodePath)
    (index : Nat)
    (fit : DataEnvironmentFitsDepth maxDepth definitions) :
    decodeListAt (decodeDataDefinitionAtWithDepth maxDepth) path index
      (definitions.map encodeDataDefinition) = .ok definitions := by
  induction definitions generalizing index with
  | nil => rfl
  | cons head tail ih =>
      have headFit : head.FitsDepth maxDepth := fit head (by simp)
      have tailFit : DataEnvironmentFitsDepth maxDepth tail := by
        intro definition member
        exact fit definition (by simp [member])
      simp only [List.map_cons, decodeListAt]
      rw [decodeDataDefinitionAtWithDepth_encodeDataDefinition maxDepth head
        (path.index index) headFit]
      rw [ih (index + 1) tailFit]
      rfl

theorem decodeDataDefinitionsAtWithDepth_encodeDataDefinitions
    (maxDepth : Nat)
    (definitions : DataEnvironment)
    (path : DecodePath)
    (fit : DataEnvironmentFitsDepth maxDepth definitions) :
    decodeDataDefinitionsAtWithDepth maxDepth path
      (encodeDataDefinitions definitions) = .ok definitions := by
  simpa [decodeDataDefinitionsAtWithDepth, encodeDataDefinitions,
    decodeArrayAt] using
      decodeDefinitionJsonListAt_encode maxDepth definitions path 0 fit

def canonicalizeDataDefinitionWithDepth
    (maxDepth : Nat)
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  (decodeDataDefinitionWithDepth maxDepth json).map encodeDataDefinition

theorem canonicalizeDataDefinitionWithDepth_of_decode_eq_ok
    (maxDepth : Nat)
    (json : Lean.Json)
    (definition : DataDefinition)
    (success : decodeDataDefinitionWithDepth maxDepth json = .ok definition) :
    canonicalizeDataDefinitionWithDepth maxDepth json =
      .ok (encodeDataDefinition definition) := by
  rw [canonicalizeDataDefinitionWithDepth, success]
  rfl

end Solcore.Core.Wire.V3
