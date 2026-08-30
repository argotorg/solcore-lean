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
    match decodeTypeWithBudget limits (encodeType type) with
    | .ok decoded =>
        assertTrue (encodeType decoded == encodeType type)
          s!"Core Wire v3 type did not round-trip: {reprStr type}"
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

  let constructor : ConstructorId := ⟨dataType, 3⟩
  assertTrue
    ((decodeConstructorId (encodeConstructorId constructor)).toOption ==
      some constructor) "constructor identity did not round-trip"
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

end Tests
