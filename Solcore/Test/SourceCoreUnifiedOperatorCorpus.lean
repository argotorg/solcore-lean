import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Checked selected unary/binary/equality methods retain their helper frontier,
mutable source cells and result coercion. Tampered-plan cases are excluded. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedOperatorCorpus
open Solcore Solcore.Frontend SourceInference
open SourceCoreUnifiedCorpusSupport

private def source : String := String.intercalate "\n" [
  "trait Witness<T> {}",
  "trait Add<T> {",
  "  function add(left: T, right: T) returns (T) where T: Witness;",
  "}",
  "trait BitNot<T> {",
  "  function bnot(value: T) returns (T) where T: Witness;",
  "}",
  "trait Eq<T> {",
  "  function eq(left: T, right: T) returns (Bool) where T: Witness;",
  "}",
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "enum Token { A, B, C }",
  "impl Witness<Token> {}",
  "impl Witness<Word> {}",
  "function rotate(value: Token) returns (Token) {",
  "  match (value) {",
  "    case .A { return .B; }",
  "    case .B { return .C; }",
  "    default { return .A; }",
  "  }",
  "}",
  "impl Add<Token> {",
  "  function add(left: Token, right: Token) returns (Token)",
  "      where Token: Witness {",
  "    let scratch: mapping(Word => Bool);",
  "    scratch[0] = false;",
  "    scratch[0] = true;",
  "    return scratch[0] ? rotate(right) : left;",
  "  }",
  "}",
  "impl BitNot<Token> {",
  "  function bnot(value: Token) returns (Token)",
  "      where Token: Witness {",
  "    let result: Token = value;",
  "    result = rotate(result);",
  "    return result;",
  "  }",
  "}",
  "impl Eq<Token> {",
  "  function eq(left: Token, right: Token) returns (Bool)",
  "      where Token: Witness {",
  "    return true;",
  "  }",
  "}",
  "impl Eq<Word> {",
  "  function eq(left: Word, right: Word) returns (Bool)",
  "      where Word: Witness {",
  "    return false;",
  "  }",
  "}",
  "impl Coerce<Token, Word> {",
  "  function coerce(value: Token) returns (Word) {",
  "    match (value) {",
  "      case .C { return 59; }",
  "      default { return 0; }",
  "    }",
  "  }",
  "}",
  "function viaAdd<T>(left: T, right: T) returns (T)",
  "    where T: Add, T: Witness {",
  "  return left + right;",
  "}",
  "function viaBitNot<T>(value: T) returns (T)",
  "    where T: BitNot, T: Witness {",
  "  return ~value;",
  "}",
  "function viaEq<T>(left: T, right: T) returns (Bool)",
  "    where T: Eq, T: Witness {",
  "  return left == right;",
  "}",
  "function binaryEntry() returns (Word) {",
  "  let left: Token = .A;",
  "  let right: Token = .B;",
  "  let result: Token = viaAdd(left, right);",
  "  match (result) {",
  "    case .C { return 31; }",
  "    default { return 0; }",
  "  }",
  "}",
  "function unaryEntry() returns (Word) {",
  "  let value: Token = .C;",
  "  let result: Token = viaBitNot(value);",
  "  match (result) {",
  "    case .A { return 41; }",
  "    default { return 0; }",
  "  }",
  "}",
  "function equalityEntry() returns (Bool) {",
  "  let left: Token = .A;",
  "  let right: Token = .B;",
  "  return viaEq(left, right);",
  "}",
  "function wordEqualityEntry() returns (Bool) {",
  "  let left: Word = 7;",
  "  let right: Word = 7;",
  "  return viaEq(left, right);",
  "}",
  "function coercedOperatorEntry() returns (Word) {",
  "  let left: Token = .A;",
  "  let right: Token = .B;",
  "  return left + right;",
  "}"
]

private def emptyGroundFastPath : IO Unit := do
  let ground ← prepare "ordinary empty-evidence fast path"
    "function leaf(value: Word) returns (Word) { return value; } function entry(value: Word) returns (Word) { return leaf(value); }"
    ["entry"]
  let owner ← key ground.sourceProgram "entry"
  let caller ← get "ordinary caller" (SourceCompilationPlan.exactSpecialization ground.indexed.base.plan owner)
  let node ← match caller.function.typedBody.nodes.findSome? (fun node => match node with
    | .expression node@{form := .call _ _ (.declaration _), ..} => some node
    | _ => none) with
    | some node => pure node | none => throw (IO.userError "ordinary direct call missing")
  assertTrue (caller.assumptions.isEmpty && node.requirements.isEmpty && node.coercions.isEmpty)
    "ordinary fast-path fixture gained evidence obligations"
  let context : SourceCoreFunctions.Context := {
    plan := ground.indexed.base.plan, owner, globals := [], administrativePrefix := 0,
    solvedRequirements := caller.function.solvedRequirements, internalReason := word 0 }
  let forbidden : SourceCoreBasic.Error := .unsupportedExpression node.id node.form
  let lowered ← get "empty evidence fast path" (SourceCoreEvidence.lowerWithProjector ground.sourceProgram
    (fun _ _ => .error forbidden) caller context (fun _ _ _ _ _ => .error forbidden)
    1 caller.function.typedBody [] node.id (fun _ => word 0))
  assertTrue lowered.isNone "empty-ground direct call lost the ordinary fast path"
  discard <| expect ground "entry" [.word (word 17)] (.word (word 17))

private def closedCallerReference : IO Unit := do
  let compiled ← prepare "closed method helper reference" (String.intercalate "\n" [
    "trait Witness<T> {}",
    "trait Add<T> { function add(left: T, right: T) returns (T) where T: Witness; }",
    "impl Witness<Word> {}",
    "function leaf(value: Word) returns (Word) { return value; }",
    "impl Add<Word> { function add(left: Word, right: Word) returns (Word) where Word: Witness { let alias: function(Word) returns(Word) = leaf; return alias(right); } }",
    "function via<T>(left: T, right: T) returns (T) where T: Add, T: Witness { return left + right; }",
    "function entry() returns (Word) { return via(2, 9); }"
  ]) ["entry"]
  discard <| expect compiled "entry" [] (.word (word 9)) 37

def run : IO Unit := do
  emptyGroundFastPath
  closedCallerReference
  let compiled ← prepare "selected operator methods" source ["binaryEntry", "unaryEntry", "equalityEntry",
    "wordEqualityEntry", "coercedOperatorEntry"]
  let binary ← expect compiled "binaryEntry" [] (.word (word 31)) 37
  assertTrue (binary.heap.any fun cell => match cell.value with
    | some (.mapping _ _ [(key, .bool value)]) => reprStr key == reprStr (SourceTypedRuntime.Value.word (word 0)) && value
    | _ => false) "selected Add method did not preserve its mutable scratch mapping"
  let unary ← expect compiled "unaryEntry" [] (.word (word 41))
  assertTrue (unary.heap.length > 2) "selected BitNot method lost its local mutation allocations"
  discard <| expect compiled "equalityEntry" [] (.bool true)
  discard <| expect compiled "wordEqualityEntry" [] (.bool false)
  let coerced ← expect compiled "coercedOperatorEntry" [] (.word (word 59)) 37
  assertTrue (!coerced.heap.isEmpty) "operator result coercion lost the method heap"
  IO.println "Core-only selected unary/binary/equality method and result coercion corpus GREEN"

end Tests.SourceCoreUnifiedOperatorCorpus
