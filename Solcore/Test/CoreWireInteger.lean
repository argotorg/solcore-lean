import Solcore.Core.Wire

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
