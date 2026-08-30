import Solcore.Core.Wire.V3.Codec.Budget
import Solcore.Core.Wire.V3.Codec.Operator

/-! Strict, budgeted type codecs for Semantic Core Wire v3. -/

set_option autoImplicit false

namespace Solcore.Core.Wire.V3

def encodeType : Ty → Lean.Json
  | .unit => "unit"
  | .bool => "bool"
  | .word => "word"
  | .product left right =>
      .mkObj [
        ("tag", "product"),
        ("left", encodeType left),
        ("right", encodeType right)
      ]
  | .function parameter result =>
      .mkObj [
        ("tag", "function"),
        ("parameter", encodeType parameter),
        ("result", encodeType result)
      ]
  | .sum left right =>
      .mkObj [
        ("tag", "sum"),
        ("left", encodeType left),
        ("right", encodeType right)
      ]
  | .cell elementType =>
      .mkObj [
        ("tag", "cell"),
        ("elementType", encodeType elementType)
      ]
  | .namedData dataType =>
      .mkObj [
        ("tag", "namedData"),
        ("dataType", encodeDataTypeId dataType)
      ]
termination_by type => sizeOf type

def typeDepth : Ty → Nat
  | .unit | .bool | .word | .namedData _ => 1
  | .product left right | .function left right | .sum left right =>
      Nat.max (typeDepth left) (typeDepth right) + 1
  | .cell elementType => typeDepth elementType + 1

def typeNodes : Ty → Nat
  | .unit | .bool | .word | .namedData _ => 1
  | .product left right | .function left right | .sum left right =>
      1 + typeNodes left + typeNodes right
  | .cell elementType => 1 + typeNodes elementType

private def decodeTypeAtFuel :
    (fuel : Nat) → (limits : CoreBudgetLimits) → CoreBudgetState → (depth : Nat) →
      fuel = limits.maxDepth + 1 - depth →
      DecodePath → Lean.Json → CoreDecodeResult (Ty × CoreBudgetState)
  | 0, limits, _, depth, exactFuel, _, _ =>
      .error (.exhausted {
        resource := .depth
        limit := limits.maxDepth
        consumed := depth
        exceeded := by
          have zeroSub : limits.maxDepth + 1 - depth = 0 := exactFuel.symm
          have bound := Nat.sub_eq_zero_iff_le.mp zeroSub
          omega
      })
  | fuel + 1, limits, state, depth, exactFuel, path, json => do
      have childFuel : fuel = limits.maxDepth + 1 - (depth + 1) := by
        omega
      let state ← consumeCoreNode limits state depth
      match json with
      | .str name =>
          match name with
          | "unit" => pure (.unit, state)
          | "bool" => pure (.bool, state)
          | "word" => pure (.word, state)
          | _ => throw (.protocol {
              path
              code := .invalidType
              arguments := .mkObj [
                ("actual", name),
                ("allowed", .arr #["unit", "bool", "word"])
              ]
            })
      | .obj _ => do
          liftProtocol <| ensureExactObject path json
            ["tag", "left", "right", "parameter", "result", "elementType",
              "dataType"] ["tag"]
          let tagPath := path.field "tag"
          let tag ← liftProtocol <| decodeStringAt tagPath
            (← liftProtocol <| requireField path json "tag")
          match tag with
          | "product" | "sum" =>
              liftProtocol <| ensureExactObject path json ["tag", "left", "right"]
                ["tag", "left", "right"]
              let (left, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "left")
                (← liftProtocol <| requireField path json "left")
              let (right, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "right")
                (← liftProtocol <| requireField path json "right")
              if tag == "product" then pure (.product left right, state)
              else pure (.sum left right, state)
          | "function" =>
              liftProtocol <| ensureExactObject path json
                ["tag", "parameter", "result"] ["tag", "parameter", "result"]
              let (parameter, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "parameter")
                (← liftProtocol <| requireField path json "parameter")
              let (result, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "result")
                (← liftProtocol <| requireField path json "result")
              pure (.function parameter result, state)
          | "cell" =>
              liftProtocol <| ensureExactObject path json ["tag", "elementType"]
                ["tag", "elementType"]
              let (elementType, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "elementType")
                (← liftProtocol <| requireField path json "elementType")
              pure (.cell elementType, state)
          | "namedData" =>
              liftProtocol <| ensureExactObject path json ["tag", "dataType"]
                ["tag", "dataType"]
              let dataType ← liftProtocol <| decodeDataTypeIdAt (path.field "dataType")
                (← liftProtocol <| requireField path json "dataType")
              pure (.namedData dataType, state)
          | _ => throw (.protocol {
              path := tagPath
              code := .invalidTag
              arguments := .mkObj [
                ("actual", tag),
                ("expected", .arr #[
                  "product", "function", "sum", "cell", "namedData"
                ])
              ]
            })
      | _ => throw (.protocol {
          path
          code := .invalidType
          arguments := .mkObj [
            ("actual", match json with
              | .null => "null" | .bool _ => "boolean" | .num _ => "number"
              | .str _ => "string" | .arr _ => "array" | .obj _ => "object"),
            ("allowed", .arr #["string", "object"])
          ]
        })

def decodeTypeAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    CoreDecodeResult (Ty × CoreBudgetState) :=
  decodeTypeAtFuel (limits.maxDepth + 1 - depth) limits state depth rfl path json

def decodeTypeWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Ty := do
  let (type, _) ← decodeTypeAtWithBudget limits .initial 1 .root json
  pure type

def decodeType (json : Lean.Json) : CoreDecodeResult Ty :=
  decodeTypeWithBudget .default json

def canonicalizeTypeWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Lean.Json :=
  encodeType <$> decodeTypeWithBudget limits json

end Solcore.Core.Wire.V3
