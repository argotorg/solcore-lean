import Solcore.Core.Wire.Codec

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
