import Solcore.Core.Wire.V3.Codec

/-! Focused scalar, identity, operator, type, and definition codec regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core.Wire.V3

private def dataType : DataTypeId := ⟨0⟩

private def types : Array Ty := #[
  .unit, .bool, .word, .product .word .bool,
  .function (.product .word .word) (.sum .unit .word),
  .sum (.cell .word) (.namedData dataType),
  .cell (.product .word .bool), .namedData dataType
]

private def unaryOps : Array UnaryOp := #[.boolNot, .wordNot, .wordClz]

private def binaryOps : Array BinaryOp := #[
  .wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod,
  .wordEq, .wordGt, .wordSgt, .wordAnd, .wordOr, .wordXor,
  .wordShl, .wordShr, .wordByte, .wordSar, .wordPow,
  .wordSignExtend, .wordSdiv, .wordSmod
]

private def ternaryOps : Array TernaryOp := #[.wordAddMod, .wordMulMod]

private def definition : DataDefinition := ⟨types.toList⟩

private def limits : CoreBudgetLimits := { maxDepth := 32, maxNodes := 1000 }

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def assertProtocol {α : Type}
    (name : String)
    (result : CoreDecodeResult α)
    (code : DecodeErrorCode)
    (pointer : String) : IO Unit := do
  match result with
  | .error (.protocol error) =>
      assertTrue (error.code == code)
        s!"{name} returned {error.code.wireName}, expected {code.wireName}"
      assertTrue (error.path.toPointer == pointer)
        s!"{name} failed at {error.path.toPointer}, expected {pointer}"
  | .error (.exhausted _) =>
      throw (IO.userError s!"{name} exhausted a Core budget")
  | .ok _ => throw (IO.userError s!"{name} unexpectedly decoded")

def testCoreWireV3CodecFoundation : IO Unit := do
  for type in types do
    let exact : CoreBudgetLimits := {
      maxDepth := typeDepth type
      maxNodes := typeNodes type
    }
    match decodeTypeAtWithBudget exact .initial 1 .root (encodeType type) with
    | .ok (decoded, state) =>
      assertTrue (encodeType decoded == encodeType type)
          s!"Core Wire v3 type did not round-trip: {reprStr type}"
      assertTrue (state.consumedNodes == typeNodes type)
        s!"Core Wire v3 type demand drifted: {reprStr type}"
    | .error _ => throw (IO.userError s!"encoded type failed: {reprStr type}")
  for op in unaryOps do
    assertTrue ((decodeUnaryOp (encodeUnaryOp op)).toOption == some op)
      s!"unary operator did not round-trip: {reprStr op}"
  for op in binaryOps do
    assertTrue ((decodeBinaryOp (encodeBinaryOp op)).toOption == some op)
      s!"binary operator did not round-trip: {reprStr op}"
  for op in ternaryOps do
    assertTrue ((decodeTernaryOp (encodeTernaryOp op)).toOption == some op)
      s!"ternary operator did not round-trip: {reprStr op}"
  match decodeBinaryOp "future" with
  | .error error =>
      assertTrue
        (error.arguments.getObjVal? "expected").isOk
        "invalid operator tag does not expose the closed expected catalog"
  | .ok _ => throw (IO.userError "unknown binary operator unexpectedly decoded")

  let constructor : ConstructorId := ⟨dataType, 3⟩
  assertTrue
    ((decodeConstructorId (encodeConstructorId constructor)).toOption ==
      some constructor) "constructor identity did not round-trip"
  match decodeConstructorId (.mkObj [
      ("index", "not-a-natural"), ("owner", "not-a-natural")
    ]) with
  | .error error =>
      assertTrue
        (error.code == .expectedNatural && error.path.toPointer == "/index")
        "constructor identity fields are not decoded in canonical key order"
  | .ok _ => throw (IO.userError "invalid constructor identity unexpectedly decoded")
  match decodeConstructorId (.mkObj [
      ("index", Lean.toJson 0), ("zzz", .null)
    ]) with
  | .error error =>
      assertTrue
        (error.code == .missingField && error.path.toPointer == "/owner")
        "exact object did not choose an earlier missing field"
  | .ok _ => throw (IO.userError "inexact constructor identity unexpectedly decoded")
  match decodeDataDefinitionWithBudget limits (encodeDataDefinition definition) with
  | .ok decoded =>
      assertTrue (encodeDataDefinition decoded == encodeDataDefinition definition)
        "data definition did not round-trip"
  | .error _ => throw (IO.userError "encoded data definition failed")
  assertTrue
    ((decodeWord (encodeWord Solcore.Core.Word.zero)).toOption ==
      some Solcore.Core.Word.zero) "zero Word did not round-trip"

  let uppercaseWord := "0x" ++ String.ofList (List.replicate 64 'A')
  match decodeWord uppercaseWord with
  | .error error =>
      assertTrue (error.arguments == .mkObj [("reason", "lowercase-hex")])
        "invalid Word reason is not closed-catalog lowercase-hex"
  | .ok _ => throw (IO.userError "uppercase Word unexpectedly decoded")
  assertProtocol "type unknown field"
    (decodeTypeWithBudget limits (.mkObj [
      ("tag", "cell"), ("elementType", "word"), ("future", .null)
    ])) .unknownField "/future"
  match decodeTypeWithBudget { maxDepth := 1, maxNodes := 10 }
      (encodeType (.product .word .word)) with
  | .error (.exhausted exhaustion) =>
      assertTrue (exhaustion.resource == .depth && exhaustion.consumed == 2)
        "nested Type did not exhaust coreDepth at demand two"
  | _ => throw (IO.userError "Type depth boundary returned the wrong result")

  let noncanonicalNatural : Lean.Json := .num { mantissa := 10, exponent := 1 }
  assertTrue
    ((canonicalizeDataTypeId noncanonicalNatural).toOption == some (Lean.toJson 1))
    "natural identity did not canonicalize"

  let invalidNaturals : List Lean.Json := [
    .num { mantissa := -1, exponent := 0 },
    .num { mantissa := 1, exponent := 1 }
  ]
  for invalidNatural in invalidNaturals do
    match decodeTypeWithBudget limits <| .mkObj [
        ("dataType", invalidNatural), ("tag", "namedData")
      ] with
    | .error (.protocol error) =>
        assertTrue
          (error.code == .expectedNatural &&
            error.arguments == .mkObj [
              ("expected", "number"), ("actual", "number")
            ])
          "expected-natural arguments are not JSON-kind exact"
    | _ => throw (IO.userError "non-natural JSON number unexpectedly decoded")

  assertProtocol "tagged union prepass precedes variant missing fields"
    (decodeTypeWithBudget limits (.mkObj [
      ("tag", "product"), ("right", "word"), ("zzz", .null)
    ])) .unknownField "/zzz"
  assertProtocol "earlier unknown field precedes missing field"
    (decodeTypeWithBudget limits (.mkObj [
      ("tag", "product"), ("right", "word"), ("aaa", .null)
    ])) .unknownField "/aaa"

end Tests
