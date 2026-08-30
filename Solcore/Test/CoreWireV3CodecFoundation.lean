import Solcore.Core.Wire.V3.Codec

/-! Focused executable regressions for the first Core Wire v3 codec slice. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core.Wire.V3

private def dataType : DataTypeId := ⟨0⟩

private def types : Array Ty := #[
  .unit,
  .bool,
  .word,
  .product .word .bool,
  .function (.product .word .word) (.sum .unit .word),
  .sum (.cell .word) (.namedData dataType),
  .cell (.product .word .bool),
  .namedData dataType
]

private def unaryOps : Array UnaryOp := #[
  .boolNot, .wordNot, .wordClz
]

private def binaryOps : Array BinaryOp := #[
  .wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod,
  .wordEq, .wordGt, .wordSgt, .wordAnd, .wordOr, .wordXor,
  .wordShl, .wordShr, .wordByte, .wordSar, .wordPow,
  .wordSignExtend, .wordSdiv, .wordSmod
]

private def ternaryOps : Array TernaryOp := #[
  .wordAddMod, .wordMulMod
]

private def definition : DataDefinition :=
  ⟨types.toList⟩

private theorem definitionFits : definition.FitsDepth 8 := by
  simp [definition, DataDefinition.FitsDepth, TypesFitDepth, types, typeDepth]

private theorem compileTimeDefinitionRoundTrip :
    decodeDataDefinitionAtWithDepth 8 .root
      (encodeDataDefinition definition) = .ok definition :=
  decodeDataDefinitionAtWithDepth_encodeDataDefinition
    8 definition .root definitionFits

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def assertError {α : Type}
    (name : String)
    (result : DecodeResult α)
    (code : DecodeErrorCode)
    (pointer : String) :
    IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"{name} unexpectedly decoded")
  | .error error =>
      assertTrue (error.code == code)
        s!"{name} returned {error.code.wireName}, expected {code.wireName}"
      assertTrue (error.path.toPointer == pointer)
        s!"{name} failed at {error.path.toPointer}, expected {pointer}"

def testCoreWireV3CodecFoundation : IO Unit := do
  for type in types do
    match decodeTypeWithDepth 8 (encodeType type) with
    | .ok decoded =>
        assertTrue (decoded == type)
          s!"Core Wire v3 type did not round-trip: {reprStr type}"
    | .error error =>
        throw (IO.userError
          s!"encoded Core Wire v3 type failed: {(Lean.toJson error).compress}")
  for op in unaryOps do
    assertTrue ((decodeUnaryOp (encodeUnaryOp op)).toOption == some op)
      s!"Core Wire v3 unary operator did not round-trip: {reprStr op}"
  for op in binaryOps do
    assertTrue ((decodeBinaryOp (encodeBinaryOp op)).toOption == some op)
      s!"Core Wire v3 binary operator did not round-trip: {reprStr op}"
  for op in ternaryOps do
    assertTrue ((decodeTernaryOp (encodeTernaryOp op)).toOption == some op)
      s!"Core Wire v3 ternary operator did not round-trip: {reprStr op}"
  let constructor : ConstructorId := ⟨dataType, 3⟩
  assertTrue
    ((decodeConstructorId (encodeConstructorId constructor)).toOption ==
      some constructor)
    "Core Wire v3 constructor identity did not round-trip"
  assertTrue
    ((decodeDataDefinitionWithDepth 8 (encodeDataDefinition definition)).toOption ==
      some definition)
    "Core Wire v3 data definition did not round-trip"
  assertTrue
    ((decodeWord (encodeWord Solcore.Core.Word.zero)).toOption ==
      some Solcore.Core.Word.zero)
    "Core Wire v3 zero Word did not round-trip"

  let uppercaseWord := "0x" ++ String.ofList (List.replicate 64 'A')
  assertError "uppercase Word" (decodeWord uppercaseWord)
    .invalidWord ""
  assertError "constructor missing index"
    (decodeConstructorId (.mkObj [("owner", 0)]))
    .missingField "/index"
  assertError "constructor unknown field"
    (decodeConstructorId (.mkObj [
      ("owner", 0), ("index", 0), ("future", .null)
    ]))
    .unknownField "/future"
  assertError "type unknown field"
    (decodeTypeWithDepth 8 (.mkObj [
      ("tag", "cell"), ("elementType", "word"), ("future", .null)
    ]))
    .unknownField "/future"
  assertError "type depth"
    (decodeTypeWithDepth 1 (encodeType (.product .word .word)))
    .depthLimitExceeded "/left"

  let noncanonicalNatural : Lean.Json :=
    .num { mantissa := 10, exponent := 1 }
  assertTrue
    ((canonicalizeDataTypeId noncanonicalNatural).toOption ==
      some (Lean.toJson 1))
    "Core Wire v3 natural identity did not canonicalize"

end Tests
