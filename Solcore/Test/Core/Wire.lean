import Solcore.Core.Wire.Codec
import Solcore.Core.Wire.Conversions
import Solcore.Core.Wire.Host
import Solcore.Core.Wire

/-!
# Core wire format tests

The canonical Core wire codec: scalars, identities, operators, types, definitions, native integers
and the host-facing wire forms.
-/

section
-- leanmerge: from Solcore.Test.CoreWireCodec
/-! End-to-end regressions for the canonical Core wire codec. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core.Wire

private def dataType : DataTypeId := ⟨0⟩
private def constructor : ConstructorId := ⟨dataType, 0⟩

private def expressions : Array Expr := #[
  .unit,
  .bool true,
  .word Solcore.Core.Word.zero,
  .var 14,
  .pair (.word Solcore.Core.Word.zero) (.bool false),
  .first (.var 0),
  .second (.var 0),
  .lambda .word .word (.var 0),
  .apply (.var 0) (.word Solcore.Core.Word.zero),
  .inLeft .word .unit,
  .inRight .unit (.word Solcore.Core.Word.zero),
  .caseE (.var 0) (.var 0) (.var 0),
  .newCell .word (.word Solcore.Core.Word.zero),
  .loadCell (.var 0),
  .storeCell (.var 0) (.word Solcore.Core.Word.zero),
  .construct constructor (.word Solcore.Core.Word.zero),
  .matchData dataType .word (.var 0)
    [(.var 0), (.word Solcore.Core.Word.zero)],
  .unary .wordClz (.word Solcore.Core.Word.zero),
  .binary .wordSdiv (.word Solcore.Core.Word.zero)
    (.word Solcore.Core.Word.zero),
  .ternary .wordAddMod (.word Solcore.Core.Word.zero)
    (.word Solcore.Core.Word.zero) (.word Solcore.Core.Word.zero),
  .letE (.word Solcore.Core.Word.zero) (.var 0),
  .ifE (.bool true) (.word Solcore.Core.Word.zero)
    (.word Solcore.Core.Word.zero)
]

private def program : Program := {
  resultType := .namedData dataType
  dataDefinitions := [⟨[.word, .product .word .bool]⟩]
  body := .construct constructor (.word Solcore.Core.Word.zero)
}

private def minimalProgram : Program := {
  resultType := .word
  dataDefinitions := []
  body := .unit
}

private def limits : CoreBudgetLimits := { maxDepth := 64, maxNodes := 10000 }

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def assertProtocol {α : Type}
    (name : String)
    (result : CoreDecodeResult α)
    (code : DecodeErrorCode)
    (pointer : String) : IO Unit := do
  match result with
  | .error (.protocol error) =>
      assertTrue (error.code == code && error.path.toPointer == pointer)
        s!"{name} returned {error.code.wireName} at {error.path.toPointer}"
  | .error (.exhausted exhaustion) =>
      throw (IO.userError s!"{name} exhausted {reprStr exhaustion.resource}")
  | .ok _ => throw (IO.userError s!"{name} unexpectedly decoded")

private def assertExhausted {α : Type}
    (name : String)
    (result : CoreDecodeResult α)
    (resource : CoreBudgetResource)
    (limit consumed : Nat) : IO Unit := do
  match result with
  | .error (.exhausted exhaustion) =>
      assertTrue
        (exhaustion.resource == resource && exhaustion.limit == limit &&
          exhaustion.consumed == consumed)
        s!"{name} returned the wrong exhaustion boundary"
  | .error (.protocol error) =>
      throw (IO.userError s!"{name} returned protocol {error.code.wireName}")
  | .ok _ => throw (IO.userError s!"{name} unexpectedly decoded")

private def programJsonWith
    (schema : String := schemaName)
    (body : Lean.Json := encodeExpr .unit) : Lean.Json :=
  .mkObj [
    ("schema", schema),
    ("resultType", encodeType .word),
    ("dataDefinitions", .arr #[]),
    ("body", body)
  ]

def testCoreWireCodec : IO Unit := do
  for expression in expressions do
    let exact : CoreBudgetLimits := {
      maxDepth := exprDepth expression
      maxNodes := exprNodes expression
    }
    match decodeExprAtWithBudget exact .initial 1 .root (encodeExpr expression) with
    | .ok (decoded, state) =>
      assertTrue (encodeExpr decoded == encodeExpr expression)
          s!"expression did not round-trip: {reprStr expression}"
      assertTrue (state.consumedNodes == exprNodes expression)
        s!"expression demand drifted: {reprStr expression}"
    | .error _ =>
        throw (IO.userError s!"encoded expression failed: {reprStr expression}")
  match decodeProgramWithBudget limits (encodeProgram program) with
  | .ok decoded =>
      assertTrue (encodeProgram decoded == encodeProgram program)
        "complete Program did not round-trip"
  | .error _ => throw (IO.userError "encoded complete Program failed")
  let exactProgram : CoreBudgetLimits := {
    maxDepth := programDepth program
    maxNodes := programNodes program
  }
  match decodeProgramAtWithBudget exactProgram .initial .root (encodeProgram program) with
  | .ok (_, state) =>
      assertTrue (state.consumedNodes == programNodes program)
        "complete Program demand drifted from its decoder"
  | .error _ => throw (IO.userError "exact complete Program budget failed")

  let noncanonicalVar : Lean.Json := .mkObj [
    ("index", .num { mantissa := 10, exponent := 1 }), ("tag", "var")
  ]
  match canonicalizeExprWithBudget limits noncanonicalVar with
  | .ok canonical =>
      assertTrue (canonical == encodeExpr (.var 1))
        "expression canonicalization did not normalize a natural"
  | .error _ => throw (IO.userError "canonicalizable expression failed")
  assertTrue ((encodeProgram minimalProgram).compress.startsWith "{\"body\":")
    "canonical object serialization is not lexicographic"

  assertProtocol "missing Program body"
    (decodeProgramWithBudget limits (.mkObj [
      ("schema", schemaName), ("resultType", "word"),
      ("dataDefinitions", .arr #[])
    ])) .missingField "/body"
  assertProtocol "lexicographically first missing Program field"
    (decodeProgramWithBudget limits (.mkObj [("schema", schemaName)]))
    .missingField "/body"
  assertProtocol "unknown expression field"
    (decodeExprWithBudget limits (.mkObj [
      ("tag", "unit"), ("future", .null)
    ])) .unknownField "/future"
  assertProtocol "invalid expression tag"
    (decodeExprWithBudget limits (.mkObj [("tag", "future")]))
    .invalidTag "/tag"
  assertProtocol "invalid Bool shape"
    (decodeExprWithBudget limits (.mkObj [
      ("tag", "bool"), ("value", "true")
    ])) .expectedBool "/value"
  let invalidBinary := .mkObj [
    ("tag", "binary"), ("op", "future"),
    ("left", .mkObj [("tag", "future")]),
    ("right", .mkObj [("tag", "future")])
  ]
  assertProtocol "operator scalar precedes unvisited children"
    (decodeExprWithBudget { maxDepth := 1, maxNodes := 1 } invalidBinary)
    .invalidTag "/op"
  let invalidApply := .mkObj [
    ("tag", "apply"),
    ("function", .mkObj [("tag", "future")]),
    ("argument", .mkObj [("tag", "future")])
  ]
  assertProtocol "child Core nodes use lexicographic fields"
    (decodeExprWithBudget { maxDepth := 2, maxNodes := 3 } invalidApply)
    .invalidTag "/argument/tag"

  assertTrue (programDepth minimalProgram == 2 && programNodes minimalProgram == 3)
    "minimal Program demand changed"
  match decodeProgramWithBudget { maxDepth := 2, maxNodes := 3 }
      (encodeProgram minimalProgram) with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "equality-at-limit rejected a valid Program")
  assertExhausted "Program depth"
    (decodeProgramWithBudget { maxDepth := 1, maxNodes := 3 }
      (encodeProgram minimalProgram)) .depth 1 2
  assertExhausted "Program nodes"
    (decodeProgramWithBudget { maxDepth := 2, maxNodes := 2 }
      (encodeProgram minimalProgram)) .nodes 2 3

  let invalidBody := .mkObj [("tag", "future")]
  assertProtocol "invalid child at node equality"
    (decodeProgramWithBudget { maxDepth := 2, maxNodes := 2 }
      (programJsonWith (body := invalidBody))) .invalidTag "/body/tag"
  assertExhausted "node excess precedes invalid child"
    (decodeProgramWithBudget { maxDepth := 2, maxNodes := 1 }
      (programJsonWith (body := invalidBody))) .nodes 1 2
  assertExhausted "depth excess precedes invalid child"
    (decodeProgramWithBudget { maxDepth := 1, maxNodes := 2 }
      (programJsonWith (body := invalidBody))) .depth 1 2
  assertProtocol "Program scalar precedes unvisited child"
    (decodeProgramWithBudget { maxDepth := 1, maxNodes := 1 }
      (programJsonWith (schema := "future") (body := invalidBody)))
    .invalidSchema "/schema"

  let located : LocatedProgramJson := { path := .root, json := encodeProgram minimalProgram }
  match decodeProgramsWithBudget { maxDepth := 2, maxNodes := 6 } [located, located] with
  | .ok (_, state) =>
      assertTrue (state.consumedNodes == 6)
        "two Programs did not share the cumulative node counter"
  | .error _ => throw (IO.userError "exact two-Program budget failed")
  assertExhausted "cross-Program cumulative nodes"
    (decodeProgramsWithBudget { maxDepth := 2, maxNodes := 5 } [located, located])
    .nodes 5 6

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreWireCodecFoundation
/-! Focused scalar, identity, operator, type, and definition codec regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core.Wire

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

private def limits_variant : CoreBudgetLimits := { maxDepth := 32, maxNodes := 1000 }

private def assertProtocol_variant {α : Type}
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

def testCoreWireCodecFoundation : IO Unit := do
  for type in types do
    let exact : CoreBudgetLimits := {
      maxDepth := typeDepth type
      maxNodes := typeNodes type
    }
    match decodeTypeAtWithBudget exact .initial 1 .root (encodeType type) with
    | .ok (decoded, state) =>
      assertTrue (encodeType decoded == encodeType type)
          s!"Core wire type did not round-trip: {reprStr type}"
      assertTrue (state.consumedNodes == typeNodes type)
        s!"Core wire type demand drifted: {reprStr type}"
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
  match decodeDataDefinitionWithBudget limits_variant (encodeDataDefinition definition) with
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
  assertProtocol_variant "type unknown field"
    (decodeTypeWithBudget limits_variant (.mkObj [
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
    match decodeTypeWithBudget limits_variant <| .mkObj [
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

  assertProtocol_variant "tagged union prepass precedes variant missing fields"
    (decodeTypeWithBudget limits_variant (.mkObj [
      ("tag", "product"), ("right", "word"), ("zzz", .null)
    ])) .unknownField "/zzz"
  assertProtocol_variant "earlier unknown field precedes missing field"
    (decodeTypeWithBudget limits_variant (.mkObj [
      ("tag", "product"), ("right", "word"), ("aaa", .null)
    ])) .unknownField "/aaa"

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreWireConversions
/-! Independent executable consumers of the canonical Core wire projection. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def dataType_variant : Wire.DataTypeId := ⟨0⟩
private def constructor_variant : Wire.ConstructorId := ⟨dataType_variant, 0⟩

private def types_variant : Array Wire.Ty := #[
  .unit,
  .bool,
  .word,
  .product .word .bool,
  .function .word .word,
  .sum .unit .word,
  .cell (.product .word .word),
  .namedData dataType_variant
]

private def expressions_variant : Array Wire.Expr := #[
  .unit,
  .bool true,
  .word Word.zero,
  .var 14,
  .pair (.word Word.zero) (.bool false),
  .first (.var 0),
  .second (.var 0),
  .lambda .word .word (.var 0),
  .apply (.var 0) (.word Word.zero),
  .inLeft .word .unit,
  .inRight .unit (.word Word.zero),
  .caseE (.var 0) (.var 0) (.var 0),
  .newCell .word (.word Word.zero),
  .loadCell (.var 0),
  .storeCell (.var 0) (.word Word.zero),
  .construct constructor_variant (.word Word.zero),
  .matchData dataType_variant .word (.var 0) [(.var 0), (.word Word.zero)],
  .unary .wordClz (.word Word.zero),
  .binary .wordSdiv (.word Word.zero) (.word Word.zero),
  .ternary .wordAddMod (.word Word.zero) (.word Word.zero) (.word Word.zero),
  .letE (.word Word.zero) (.var 0),
  .ifE (.bool true) (.word Word.zero) (.word Word.zero)
]

private def unaryOps_variant : Array Wire.UnaryOp := #[
  .boolNot, .wordNot, .wordClz
]

private def binaryOps_variant : Array Wire.BinaryOp := #[
  .wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod,
  .wordEq, .wordGt, .wordSgt, .wordAnd, .wordOr, .wordXor,
  .wordShl, .wordShr, .wordByte, .wordSar, .wordPow,
  .wordSignExtend, .wordSdiv, .wordSmod
]

private def ternaryOps_variant : Array Wire.TernaryOp := #[
  .wordAddMod, .wordMulMod
]

private def program_variant : Wire.Program := {
  resultType := .namedData dataType_variant
  dataDefinitions := [⟨[.word, .product .word .bool]⟩]
  body := .construct constructor_variant (.word Word.zero)
}

private theorem compileTimeProgramRoundTrip :
    Wire.Program.ofCore? program_variant.toCore = some program_variant := by
  simp

private def allRoundTrips : Bool :=
  (types_variant.all fun type => Wire.Ty.ofCore? type.toCore == some type) &&
  (expressions_variant.all fun expression =>
    Wire.Expr.ofCore? expression.toCore == some expression) &&
  (unaryOps_variant.all fun op => Wire.UnaryOp.ofCore? op.toCore == some op) &&
  (binaryOps_variant.all fun op => Wire.BinaryOp.ofCore? op.toCore == some op) &&
  (ternaryOps_variant.all fun op => Wire.TernaryOp.ofCore? op.toCore == some op) &&
  (Wire.Program.ofCore? program_variant.toCore == some program_variant)

def testCoreWireConversions : IO Unit := do
  assertTrue allRoundTrips
    "Core wire stopped round-tripping a published constructor"

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreWireHost
/-! Focused regressions for the canonical Semantic Core wire host boundary. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Core.Wire

private def storageReadProgram : Solcore.Core.Program := {
  resultType := .word
  body :=
    .apply (.var HostFunction.storageRead.index) (.word Word.zero)
}

private def shiftedStorageReadProgram : Solcore.Core.Program := {
  resultType := .word
  body :=
    .letE .unit
      (.apply (.var (HostFunction.storageRead.index + 1)) (.word Word.zero))
}

private def unshiftedStorageReadProgram : Solcore.Core.Program := {
  resultType := .word
  body :=
    .letE .unit
      (.apply (.var HostFunction.storageRead.index) (.word Word.zero))
}

private def firstUnboundProgram : Solcore.Core.Program := {
  resultType := .word
  body := .var 14
}

private def wireStorageReadProgram : Solcore.Core.Wire.Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (.var 0) (.word Word.zero)
}

private def wireFirstUnboundProgram : Solcore.Core.Wire.Program := {
  resultType := .word
  dataDefinitions := []
  body := .var 14
}

example : Host.functions =
    [.storageRead, .storageWrite, .storageAddress, .codeAddress,
      .callValue, .callerAddress, .inputDataByte?, .inputDataSize,
      .inputDataWordBE?, .currentAddress, .callContractWord,
      .callContractWordWithValue, .createContractWord, .emitLogWord] :=
  rfl

example : Host.context[13]? =
    some (HostFunction.functionType .emitLogWord) :=
  Host.context_lookup .emitLogWord

example : Host.environment[13]? =
    some (.hostFunction .emitLogWord) :=
  Host.environment_lookup .emitLogWord

example : Host.check storageReadProgram = true := by
  decide

example : Host.checkDetailed storageReadProgram = .ok .word := by
  rfl

example : Host.check shiftedStorageReadProgram = true := by
  decide

example : Host.check unshiftedStorageReadProgram = false := by
  decide

example : Host.check firstUnboundProgram = false := by
  decide

example : storageReadProgram.checkHost = true :=
  Host.check_promotes_current (by decide)

example : wireStorageReadProgram.check = true := by
  native_decide

example : wireStorageReadProgram.checkDetailed = .ok .word := by
  apply Solcore.Core.Wire.Program.checkDetailed_iff_check.mpr
  native_decide

example : wireFirstUnboundProgram.check = false := by
  native_decide

example : wireStorageReadProgram.toCore.checkHost = true :=
  Solcore.Core.Wire.Program.check_promotes_current (by native_decide)

def testCoreWireHost : IO Unit := do
  assertTrue (Host.functions.length == 14)
    "Semantic Core wire must expose exactly fourteen host functions"
  assertTrue
    (Host.context == hostContext &&
      Host.environment == hostEnvironment)
    "the wire host entries must match the current internal prefix"
  assertTrue (Host.check storageReadProgram)
    "the frozen checker rejected a root host consumer"
  assertTrue (Host.check shiftedStorageReadProgram)
    "a local binder did not shift the frozen host context"
  assertTrue (!Host.check unshiftedStorageReadProgram)
    "an unshifted host index resolved through a local binder"
  assertTrue (!Host.check firstUnboundProgram)
    "the frozen checker accepted the first unbound root index"
  assertTrue wireStorageReadProgram.check
    "the Wire checker rejected its projected host consumer"
  assertTrue (!wireFirstUnboundProgram.check)
    "the Wire checker accepted the first unbound root index"
  match Host.checkDetailed storageReadProgram with
  | .ok .word => pure ()
  | result =>
      throw (IO.userError
        s!"the frozen detailed checker returned {reprStr result}")

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreWireInteger
/-! Native Integer Wire syntax, canonical spellings, and pre-parse resource limits. -/

set_option autoImplicit false

namespace Tests.CoreWireInteger

open Solcore.Core.Wire

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def assertProtocol {α : Type} (result : CoreDecodeResult α)
    (code : DecodeErrorCode) (pointer : String) : IO Unit := do
  match result with
  | .error (.protocol error) =>
      assertTrue (error.code == code && error.path.toPointer == pointer)
        s!"wrong Integer protocol error: {error.code.wireName} at {error.path.toPointer}"
  | _ => throw (IO.userError "expected an Integer protocol error")

private def assertBudget {α : Type} (result : CoreDecodeResult α)
    (resource : CoreBudgetResource) (limit consumed : Nat) : IO Unit := do
  match result with
  | .error (.exhausted exhaustion) =>
      assertTrue (exhaustion.resource == resource && exhaustion.limit == limit &&
        exhaustion.consumed == consumed) "wrong Integer budget exhaustion"
  | _ => throw (IO.userError "expected an Integer budget exhaustion")

private def literal (value : Lean.Json) : Lean.Json :=
  .mkObj [("tag", "integer"), ("value", value)]

private def huge : Int := (2 : Int) ^ 1024 + 123456789

private def values : Array Int := #[0, 1, -1, 256, -256, huge, -huge]

private def unaryOps : Array UnaryOp := #[.integerNot, .integerToWord, .wordToInteger]

private def binaryOps : Array BinaryOp := #[
  .integerAdd, .integerSub, .integerMul, .integerDiv, .integerMod,
  .integerEq, .integerLt, .integerAnd, .integerOr, .integerXor
]

private def expressions : Array Expr := #[
  .integer (-huge),
  .pair (.integer huge) (.integer (-17)),
  .newCell .integer (.integer (-13)),
  .lambda .integer .integer (.binary .integerAdd (.var 0) (.integer 1)),
  .inRight .unit (.integer 0),
  .matchData ⟨0⟩ .integer (.construct ⟨⟨0⟩, 0⟩ (.integer (-7))) [.var 0],
  .unary .integerToWord (.integer (-1)),
  .unary .wordToInteger (.word Solcore.Core.Word.zero)
]

private def program : Program := {
  resultType := .integer
  dataDefinitions := [⟨[.integer, .function .integer .integer]⟩]
  body := .binary .integerAdd (.integer huge) (.integer (-1))
}

example : program.check = true := by native_decide

example (expression : Expr) : Expr.ofCore? expression.toCore = some expression := by simp
example : Ty.ofCore? .integer = some .integer := rfl
example : Expr.ofCore? (.integer (-7)) = some (.integer (-7)) := by simp [Expr.ofCore?]

example {limits : CoreBudgetLimits} {state finalState : CoreBudgetState}
    {path : DecodePath} {text : String} {value : Int}
    (accepted : decodeIntegerTextAtWithBudget limits state path text = .ok (value, finalState)) :
    encodeIntegerText value = text :=
  encodeIntegerText_of_decodeIntegerTextAtWithBudget_eq_ok limits state finalState path text value accepted

-- Updating the node counter must retain Integer bytes already consumed.
example : consumeCoreNode { maxDepth := 1, maxNodes := 1 }
    { consumedIntegerBytes := 73 } 1 = .ok { consumedNodes := 1, consumedIntegerBytes := 73 } := rfl

-- Byte exhaustion has priority over parsing an invalid, oversized spelling.
example : decodeIntegerTextAtWithBudget
    { maxDepth := 1, maxNodes := 1, maxIntegerBytes := 1 } .initial .root "bad" =
    .error (.exhausted {
      resource := .integerBytes
      limit := 1
      consumed := 3
      exceeded := by decide
    }) := rfl

def run : IO Unit := do
  for value in values do
    assertTrue ((decodeInteger (encodeInteger value)).toOption == some value)
      "Integer scalar did not round-trip"
    assertTrue (encodeInteger value == Lean.Json.str (toString value))
      "Integer scalar was encoded as a JSON number"
    assertTrue ((canonicalizeIntegerWithBudget .default (encodeInteger value)).toOption ==
      some (encodeInteger value)) "Integer scalar canonicalization changed its spelling"
    let expression := Expr.integer value
    let bytes := exprIntegerBytes expression
    let exact : CoreBudgetLimits := { maxDepth := 1, maxNodes := 1, maxIntegerBytes := bytes }
    match decodeExprAtWithBudget exact .initial 1 .root (encodeExpr expression) with
    | .ok (decoded, state) =>
        assertTrue (decoded == expression && state.consumedNodes == 1 &&
          state.consumedIntegerBytes == bytes) "Integer literal demand or round-trip drifted"
    | _ => throw (IO.userError "Integer literal failed at its exact budget")
    assertBudget (decodeExprWithBudget { exact with maxIntegerBytes := bytes - 1 }
      (encodeExpr expression)) .integerBytes (bytes - 1) bytes

  for type in #[Ty.integer, .cell .integer, .product .integer .word,
      .function .integer (.sum .integer .unit)] do
    assertTrue ((decodeType (encodeType type)).toOption == some type)
      "Integer type did not round-trip"
    assertTrue (Ty.ofCore? type.toCore == some type) "Integer type projection changed"
  for op in unaryOps do
    assertTrue ((decodeUnaryOp (encodeUnaryOp op)).toOption == some op)
      "Integer unary tag did not round-trip"
    assertTrue (UnaryOp.ofCore? op.toCore == some op) "Integer unary projection changed"
  for op in binaryOps do
    assertTrue ((decodeBinaryOp (encodeBinaryOp op)).toOption == some op)
      "Integer binary tag did not round-trip"
    assertTrue (BinaryOp.ofCore? op.toCore == some op) "Integer binary projection changed"
    let expression := Expr.binary op (.integer (-huge)) (.integer 3)
    assertTrue ((decodeExpr (encodeExpr expression)).toOption == some expression)
      "Integer binary expression did not round-trip"
  for expression in expressions do
    let exact : CoreBudgetLimits := {
      maxDepth := exprDepth expression
      maxNodes := exprNodes expression
      maxIntegerBytes := exprIntegerBytes expression
    }
    match decodeExprAtWithBudget exact .initial 1 .root (encodeExpr expression) with
    | .ok (decoded, state) =>
        assertTrue (decoded == expression && state.consumedNodes == exprNodes expression &&
          state.consumedIntegerBytes == exprIntegerBytes expression)
          "nested Integer expression demand or round-trip drifted"
    | _ => throw (IO.userError "nested Integer expression failed at exact budget")

  for text in #["", "-", "+1", "01", "-01", "-0", "00", "1_0", "0_1", "-0_1",
      " 1", "1 ", "1.0", "1e3", "0xff", "１２", "--1"] do
    assertProtocol (decodeExpr (literal (.str text))) .invalidInteger "/value"
  assertProtocol (decodeExpr (literal (Lean.toJson (7 : Nat)))) .expectedString "/value"
  assertProtocol (decodeExpr (literal .null)) .expectedString "/value"
  assertProtocol (decodeExpr (.mkObj [("tag", "integer")])) .missingField "/value"
  assertProtocol (decodeExpr (.mkObj [("tag", "integer"), ("value", "1"), ("extra", .null)]))
    .unknownField "/extra"
  assertProtocol (decodeExpr (.mkObj [("tag", "Integer"), ("value", "1")])) .invalidTag "/tag"

  let oversized := String.ofList (List.replicate 10000 '9')
  assertBudget (decodeExprWithBudget { maxDepth := 1, maxNodes := 1, maxIntegerBytes := 64 }
    (literal (.str oversized))) .integerBytes 64 10000
  let oversizedMalformed := String.ofList (List.replicate 10000 'x')
  assertBudget (decodeExprWithBudget { maxDepth := 1, maxNodes := 1, maxIntegerBytes := 64 }
    (literal (.str oversizedMalformed))) .integerBytes 64 10000
  assertBudget (decodeIntegerWithBudget { maxDepth := 0, maxNodes := 0, maxIntegerBytes := 2 }
    "１２") .integerBytes 2 6
  assertBudget (decodeExprWithBudget { maxDepth := 1, maxNodes := 0, maxIntegerBytes := 0 }
    (literal "bad")) .nodes 0 1
  assertBudget (decodeExprWithBudget { maxDepth := 0, maxNodes := 0, maxIntegerBytes := 0 }
    (literal "bad")) .depth 0 1

  let exact : CoreBudgetLimits := {
    maxDepth := programDepth program
    maxNodes := programNodes program
    maxIntegerBytes := programIntegerBytes program
  }
  match decodeProgramAtWithBudget exact .initial .root (encodeProgram program) with
  | .ok (decoded, state) =>
      assertTrue (decoded == program && state.consumedNodes == programNodes program &&
        state.consumedIntegerBytes == programIntegerBytes program)
        "Integer Program demand or round-trip drifted"
      assertTrue decoded.check "decoded Integer Program failed Core checking"
  | _ => throw (IO.userError "Integer Program failed at its exact budget")
  let located : LocatedProgramJson := { path := DecodePath.root.index 0, json := encodeProgram program }
  match decodeProgramsWithBudget {
    exact with
    maxNodes := 2 * exact.maxNodes
    maxIntegerBytes := 2 * exact.maxIntegerBytes
  } [located, located] with
  | .ok (decoded, state) =>
      assertTrue (decoded == [program, program] &&
        state.consumedIntegerBytes == 2 * exact.maxIntegerBytes &&
        state.consumedNodes == 2 * exact.maxNodes) "Integer package budgets are not cumulative"
  | _ => throw (IO.userError "Integer package failed at its exact budget")
  let firstLiteralBytes := (encodeIntegerText huge).utf8ByteSize
  assertBudget (decodeProgramsWithBudget { exact with maxNodes := 2 * exact.maxNodes }
    [located, located]) .integerBytes exact.maxIntegerBytes (exact.maxIntegerBytes + firstLiteralBytes)

  -- A saved byte count survives type traversal and then charges the next literal.
  match decodeTypeAtWithBudget { maxDepth := 1, maxNodes := 2, maxIntegerBytes := 5 }
      { consumedNodes := 1, consumedIntegerBytes := 4 } 1 .root "integer" with
  | .ok (_, state) =>
      assertTrue (state.consumedIntegerBytes == 4) "type decoder reset Integer byte budget"
      assertBudget (decodeIntegerAtWithBudget { maxDepth := 1, maxNodes := 2, maxIntegerBytes := 5 }
        state .root "12") .integerBytes 5 6
  | _ => throw (IO.userError "saved Integer byte count failed type traversal")

  -- Pinned old JSON remains readable and re-encodes without new fields or tags.
  let oldJson : Lean.Json := .mkObj [
    ("schema", "solcore-semantic-core"), ("resultType", "word"),
    ("dataDefinitions", .arr #[]),
    ("body", .mkObj [("tag", "word"),
      ("value", "0x0000000000000000000000000000000000000000000000000000000000000000")])
  ]
  match decodeProgram oldJson with
  | .ok oldProgram =>
      assertTrue (encodeProgram oldProgram == oldJson)
        "native Integer support changed pinned old JSON"
  | _ => throw (IO.userError "native Integer support rejected pinned old JSON")
  assertProtocol (decodeExpr (.mkObj [("tag", "integerLiteral"), ("value", "1")]))
    .invalidTag "/tag"
  assertProtocol (decodeType "Integer") .invalidType ""

end Tests.CoreWireInteger
end

section
-- leanmerge: from Solcore.Test.CoreWirePublic
/-! The public Wire umbrella exposes conversion, checking, and JSON APIs. -/

set_option autoImplicit false

namespace Tests

namespace CoreWirePublic

open Solcore.Core.Wire

private def program : Program := {
  resultType := .word
  dataDefinitions := []
  body := .word Solcore.Core.Word.zero
}

example : program.toCore.resultType = .word := by rfl

example : program.check = true := by native_decide

example : Host.functions.length = 14 := by decide

def testCoreWirePublic : IO Unit := do
  match decodeProgram (encodeProgram program) with
  | .ok decoded =>
      unless encodeProgram decoded == encodeProgram program do
        throw (IO.userError "public Wire codec did not round-trip")
  | .error _ =>
      throw (IO.userError "public Wire umbrella failed to decode its Program")

end CoreWirePublic

end Tests
end
