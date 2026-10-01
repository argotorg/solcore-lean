import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Checker-produced control, assignment order and native scalar programs,
ported from the executable typed-runtime corpus. Trusted IR rewrites are absent. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedControlCorpus
open Solcore Solcore.Frontend SourceInference
open SourceCoreUnifiedCorpusSupport

private def source : String := String.intercalate "\n" [
  "function assignments() returns (Word) { let local: Word = 5; local += 3; local ~=; return local; }",
  "function mappings() returns (Word) { let table: mapping(Word => Word); let before: Word = table[7]; table[7] = 4; table[7] += 3; let nested: mapping(Word => mapping(Word => Word)); nested[1][2] = 9; return before + table[7] + nested[1][2]; }",
  "function loops() returns (Word) { let total: Word = 0; let i: Word = 0; while (i < 5) { i += 1; if (i == 2) { continue; } if (i == 4) { break; } total += i; } for (let j: Word = 0; j < 4; j += 1) { if (j == 1) { continue; } if (j == 3) { break; } total += j; } return total; }",
  "function assignmentOrder() returns (Word) { let order: Word = 0; let table: mapping(Word => Word); let indexer = lam() -> Word { order = order * 10 + 1; return 5; }; let rhs = lam() -> Word { order = order * 10 + 2; return 7; }; table[indexer()] = rhs(); return order * 100 + table[5]; }",
  "function compoundSnapshot() returns (Word) { let value: Word = 5; let rhs = lam() -> Word { value = 20; return 3; }; value += rhs(); return value; }",
  "function targetFailure() returns (Word) { let order: Word = 0; let table: mapping(Word => Word); let indexer = lam() -> Word { order = 1; let absent: Word; return absent; }; let rhs = lam() -> Word { order = 2; return 7; }; table[indexer()] = rhs(); return order; }",
  "function rhsFailure() returns (Word) { let target: Word; let rhs = lam() -> Word { let absent: Word; return absent; }; target += rhs(); return 0; }",
  "function unaryAbsent() returns (Word) { let target: Word; target ~=; return 0; }",
  "function integerBitNot() returns (integer) { return ~5; }",
  "function integerBitAndNegative() returns (integer) { return integerSub(0, 5) & 3; }",
  "function integerBitOrNegative() returns (integer) { return 2 | integerSub(0, 5); }",
  "function integerBitXorNegative() returns (integer) { return integerSub(0, 5) ^ 2; }",
  "function descend(value: Word) returns (Word) { return value == 0 ? 9 : descend(value - 1); }",
  "function even(value: Word) returns (Bool) { return value == 0 ? true : odd(value - 1); }",
  "function odd(value: Word) returns (Bool) { return value == 0 ? false : even(value - 1); }",
  "function implicitTail() returns (Word) { 40 + 2 }",
  "function spin(value: Word) returns (Word) { return spin(value); }"
]

private def binder (compiled : Compiled) (name localName : String) : IO Resolved.LocalId := do
  let owner ← key compiled.sourceProgram name
  let function ← get "fault binder specialization" (SourceCompilationPlan.exactSpecialization compiled.validationPlan owner)
  match (SourceCoreDataPlaces.declaredBinders function.function.typedBody).filter (·.name == localName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"{name} exact fault binder missing")

def run : IO Unit := do
  let compiled ← prepare "control/order" source ["assignments", "mappings", "loops", "assignmentOrder",
    "compoundSnapshot", "targetFailure", "rhsFailure", "unaryAbsent", "integerBitNot",
    "integerBitAndNegative", "integerBitOrNegative", "integerBitXorNegative", "descend", "even", "implicitTail", "spin"]
  let assignments ← expect compiled "assignments" [] (.word (Core.Word.maximum.sub (word 8)))
  assertTrue (assignments.heap.length == 1) "bit-not source allocation changed"
  let mappings ← expect compiled "mappings" [] (.word (word 16))
  assertTrue (mappings.heap.length == 3 && hasWord mappings 0) "nested/default mapping source allocations changed"
  for spent in [0, 43, 300000] do
    discard <| expect compiled "loops" [] (.word (word 6)) spent
  let ordered ← expect compiled "assignmentOrder" [] (.word (word 1207))
  assertTrue (hasWord ordered 12) "index/RHS source writes were lost"
  let snapshot ← expect compiled "compoundSnapshot" [] (.word (word 8))
  assertTrue (hasWord snapshot 8 && !hasWord snapshot 20) "compound assignment did not use the pre-RHS snapshot"
  for (name, expected) in [("integerBitNot", -6), ("integerBitAndNegative", 3),
      ("integerBitOrNegative", -5), ("integerBitXorNegative", -7)] do
    let state ← expect compiled name [] (.integer expected)
    assertTrue state.heap.isEmpty s!"{name} unexpectedly allocated source cells"
  discard <| expect compiled "descend" [.word (word 5)] (.word (word 9)) 41
  discard <| expect compiled "even" [.word (word 6)] (.bool true) 41
  discard <| expect compiled "even" [.word (word 5)] (.bool false)
  discard <| expect compiled "implicitTail" [] (.word (word 42))
  for name in ["targetFailure", "rhsFailure"] do
    let absent ← binder compiled name "absent"
    let result ← execute compiled name
    match result.observation with
    | .fault error state =>
      assertTrue (error == .uninitializedLocal absent) s!"{name} source fault priority or binder changed"
      if name == "targetFailure" then
        assertTrue (hasWord state 1 && !hasWord state 2) "RHS ran after target fault"
    | other => throw (IO.userError s!"{name} source fault changed: {reprStr other}")
  let unary ← execute compiled "unaryAbsent"
  match unary.observation with
  | .fault error _ => assertTrue (error == .invalidUnaryOperand .bitNot none) "bit-not absence diagnostic changed"
  | other => throw (IO.userError s!"missing unary operand returned {reprStr other}")
  let first ← execute compiled "spin" [.word (word 3)] 1200
  let second ← get "recursive spin native resume" (SourceCoreUnifiedCompilation.Result.resume first 1200)
  for result in [first, second] do
    match result.observation with
    | .outOfFuel state => assertTrue (!state.heap.isEmpty) "recursive spin lost source parameter cells"
    | other => throw (IO.userError s!"recursive spin falsely terminated: {reprStr other}")
  IO.println "Core-only checked control, scalar operators, target/RHS order, faults and recursion corpus GREEN"

end Tests.SourceCoreUnifiedControlCorpus
