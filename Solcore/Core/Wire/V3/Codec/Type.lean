import Solcore.Core.Wire.V3.Codec.Operator

/-! Strict, depth-bounded type codecs for Semantic Core Wire v3. -/

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

def defaultTypeDepth : Nat := 1024

def decodeTypeAtWithDepth :
    Nat → DecodePath → Lean.Json → DecodeResult Ty
  | 0, path, _ =>
      failAt path .depthLimitExceeded (.mkObj [("limit", 0)])
  | depth + 1, path, json =>
      match json with
      | .str name =>
          match name with
          | "unit" => pure .unit
          | "bool" => pure .bool
          | "word" => pure .word
          | _ =>
              failAt path .invalidType (.mkObj [
                ("actual", name),
                ("allowed", .arr #["unit", "bool", "word"])
              ])
      | .obj _ => do
          ensureExactObject path json
            ["tag", "left", "right", "parameter", "result", "elementType",
              "dataType"]
            ["tag"]
          let tagPath := path.field "tag"
          let tag ← decodeStringAt tagPath (← requireField path json "tag")
          match tag with
          | "product" =>
              ensureExactObject path json ["tag", "left", "right"]
                ["tag", "left", "right"]
              let left ← decodeTypeAtWithDepth depth (path.field "left")
                (← requireField path json "left")
              let right ← decodeTypeAtWithDepth depth (path.field "right")
                (← requireField path json "right")
              pure (.product left right)
          | "function" =>
              ensureExactObject path json ["tag", "parameter", "result"]
                ["tag", "parameter", "result"]
              let parameter ← decodeTypeAtWithDepth depth (path.field "parameter")
                (← requireField path json "parameter")
              let result ← decodeTypeAtWithDepth depth (path.field "result")
                (← requireField path json "result")
              pure (.function parameter result)
          | "sum" =>
              ensureExactObject path json ["tag", "left", "right"]
                ["tag", "left", "right"]
              let left ← decodeTypeAtWithDepth depth (path.field "left")
                (← requireField path json "left")
              let right ← decodeTypeAtWithDepth depth (path.field "right")
                (← requireField path json "right")
              pure (.sum left right)
          | "cell" =>
              ensureExactObject path json ["tag", "elementType"]
                ["tag", "elementType"]
              let elementType ←
                decodeTypeAtWithDepth depth (path.field "elementType")
                  (← requireField path json "elementType")
              pure (.cell elementType)
          | "namedData" =>
              ensureExactObject path json ["tag", "dataType"]
                ["tag", "dataType"]
              let dataType ← decodeDataTypeIdAt (path.field "dataType")
                (← requireField path json "dataType")
              pure (.namedData dataType)
          | _ =>
              failAt tagPath .invalidTag (.mkObj [
                ("actual", tag),
                ("allowed", .arr #[
                  "product", "function", "sum", "cell", "namedData"
                ])
              ])
      | _ =>
          failAt path .invalidType (.mkObj [
            ("expected", "scalar type string or composite type object")
          ])

def decodeTypeWithDepth
    (maxDepth : Nat)
    (json : Lean.Json) :
    DecodeResult Ty :=
  decodeTypeAtWithDepth maxDepth .root json

def decodeType (json : Lean.Json) : DecodeResult Ty :=
  decodeTypeWithDepth defaultTypeDepth json

def canonicalizeTypeWithDepth
    (maxDepth : Nat)
    (json : Lean.Json) :
    DecodeResult Lean.Json :=
  (decodeTypeWithDepth maxDepth json).map encodeType

end Solcore.Core.Wire.V3
