import Solcore.Core.Wire.Codec.TypeProperties

/-! Data-definition codecs with shared Core-node accounting. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

def encodeTypeList (types : List Ty) : Lean.Json :=
  .arr (types.map encodeType).toArray

private def decodeTypeJsonListAtWithBudget
    (limits : CoreBudgetLimits)
    (depth : Nat)
    (path : DecodePath) :
    Nat → CoreBudgetState → List Lean.Json →
      CoreDecodeResult (List Ty × CoreBudgetState)
  | _, state, [] => pure ([], state)
  | index, state, json :: rest => do
      let (type, state) ← decodeTypeAtWithBudget limits state depth
        (path.index index) json
      let (types, state) ← decodeTypeJsonListAtWithBudget limits depth path
        (index + 1) state rest
      pure (type :: types, state)

def decodeTypeListAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    CoreDecodeResult (List Ty × CoreBudgetState) := do
  let values ← liftProtocol <|
    match json with
    | .arr values => pure values.toList
    | _ => failAt path .expectedArray (.mkObj [
        ("expected", "array"),
        ("actual", match json with
          | .null => "null" | .bool _ => "boolean" | .num _ => "number"
          | .str _ => "string" | .arr _ => "array" | .obj _ => "object")
      ])
  decodeTypeJsonListAtWithBudget limits depth path 0 state values

def encodeDataDefinition (definition : DataDefinition) : Lean.Json :=
  .mkObj [
    ("constructorPayloadTypes",
      encodeTypeList definition.constructorPayloadTypes)
  ]

def decodeDataDefinitionAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    CoreDecodeResult (DataDefinition × CoreBudgetState) := do
  let state ← consumeCoreNode limits state depth
  liftProtocol <| ensureExactObject path json ["constructorPayloadTypes"]
    ["constructorPayloadTypes"]
  let (payloadTypes, state) ← decodeTypeListAtWithBudget limits state (depth + 1)
    (path.field "constructorPayloadTypes")
    (← liftProtocol <| requireField path json "constructorPayloadTypes")
  pure ({ constructorPayloadTypes := payloadTypes }, state)

def decodeDataDefinitionWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult DataDefinition := do
  let (definition, _) ←
    decodeDataDefinitionAtWithBudget limits .initial 1 .root json
  pure definition

def encodeDataDefinitions (definitions : DataEnvironment) : Lean.Json :=
  .arr (definitions.map encodeDataDefinition).toArray

private def decodeDefinitionJsonListAtWithBudget
    (limits : CoreBudgetLimits)
    (depth : Nat)
    (path : DecodePath) :
    Nat → CoreBudgetState → List Lean.Json →
      CoreDecodeResult (DataEnvironment × CoreBudgetState)
  | _, state, [] => pure ([], state)
  | index, state, json :: rest => do
      let (definition, state) ← decodeDataDefinitionAtWithBudget limits state depth
        (path.index index) json
      let (definitions, state) ← decodeDefinitionJsonListAtWithBudget
        limits depth path (index + 1) state rest
      pure (definition :: definitions, state)

def decodeDataDefinitionsAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    CoreDecodeResult (DataEnvironment × CoreBudgetState) := do
  let values ← liftProtocol <|
    match json with
    | .arr values => pure values.toList
    | _ => failAt path .expectedArray (.mkObj [
        ("expected", "array"),
        ("actual", match json with
          | .null => "null" | .bool _ => "boolean" | .num _ => "number"
          | .str _ => "string" | .arr _ => "array" | .obj _ => "object")
      ])
  decodeDefinitionJsonListAtWithBudget limits depth path 0 state values

def typeListDepth : List Ty → Nat
  | [] => 0
  | type :: rest => Nat.max (typeDepth type) (typeListDepth rest)

def typeListNodes : List Ty → Nat
  | [] => 0
  | type :: rest => typeNodes type + typeListNodes rest

def dataDefinitionDepth (definition : DataDefinition) : Nat :=
  Nat.max 1 (typeListDepth definition.constructorPayloadTypes + 1)

def dataDefinitionNodes (definition : DataDefinition) : Nat :=
  1 + typeListNodes definition.constructorPayloadTypes

def dataEnvironmentDepth : DataEnvironment → Nat
  | [] => 0
  | definition :: rest =>
      Nat.max (dataDefinitionDepth definition) (dataEnvironmentDepth rest)

def dataEnvironmentNodes : DataEnvironment → Nat
  | [] => 0
  | definition :: rest =>
      dataDefinitionNodes definition + dataEnvironmentNodes rest

def canonicalizeDataDefinitionWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Lean.Json :=
  encodeDataDefinition <$> decodeDataDefinitionWithBudget limits json

theorem canonicalizeDataDefinitionWithBudget_of_decode_eq_ok
    (limits : CoreBudgetLimits)
    (json : Lean.Json)
    (definition : DataDefinition)
    (success : decodeDataDefinitionWithBudget limits json = .ok definition) :
    canonicalizeDataDefinitionWithBudget limits json =
      .ok (encodeDataDefinition definition) := by
  rw [canonicalizeDataDefinitionWithBudget, success]
  rfl

end Solcore.Core.Wire
