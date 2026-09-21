import Solcore

/-!
Whole-program rejection and resource-boundary regressions for direct
Core-representable staged calls.

Unlike the carrier-level tamper suite, these cases use only checked source and
the public preparation boundary.  They fix which unsupported call features
fail explicitly and ensure finite specialization does not make recursive
staged evaluation appear executable.
-/

set_option autoImplicit false

namespace Tests.SourceStagedValueCallsTamper

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceProgramExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | none => throw (IO.userError
      "invalid staged-value call boundary module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def limits (specializationBudget : Nat) : Limits := {
  checkingFuel := 1024
  specializationBudget
  executionFuel := 4096
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def predicateSource : String := String.intercalate "\n" [
  "trait Marker<T> {}",
  "impl Marker<Word> {}",
  "function marked(comptime value: Word) returns (comptime<Word>) where Word: Marker {",
  "  return value;",
  "}",
  "function entry() returns (Word) { return marked(3); }"
]

private def testPredicateRejected : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace predicateSource) (Seed.named moduleId "entry")
      (limits 2) with
  | .error (.linking (.stagedValueCallPredicatesUnsupported
      _ _ predicates)) =>
      assertTrue (!predicates.isEmpty)
        "predicate-bearing rejection lost its exact predicate list"
  | result => throw (IO.userError
      s!"predicate-bearing marked call was not rejected: {reprStr result}")

private def coercionSource : String := String.intercalate "\n" [
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) {",
  "    return value ? 41 : 7;",
  "  }",
  "}",
  "function staged() returns (comptime<Bool>) { return true; }",
  "function entry() returns (Word) { return staged(); }"
]

private def testResultCoercionRejected : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace coercionSource) (Seed.named moduleId "entry")
      (limits 2) with
  | .error (.linking (.sourceCore error)) =>
      match error.reason with
      | .coercionsPresent coercions =>
          assertTrue (!coercions.isEmpty)
            "result-coercion rejection lost its coercion path"
      | reason => throw (IO.userError
          s!"marked result coercion failed for the wrong reason: {reprStr reason}")
  | result => throw (IO.userError
      s!"a coerced marked result escaped staged evaluation: {reprStr result}")

private def expectRecursiveCall (label content root : String)
    (budget : Nat) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId root)
      (limits budget) with
  | .error (.linking (.recursiveCallCycle _)) => pure ()
  | result => throw (IO.userError
      s!"{label}: recursive staged call was not rejected: {reprStr result}")

private def selfRecursiveSource : String := String.intercalate "\n" [
  "function loop(comptime value: Word) returns (comptime<Word>) {",
  "  return loop(value);",
  "}",
  "function entry() returns (Word) { return loop(1); }"
]

private def mutualRecursiveSource : String := String.intercalate "\n" [
  "function left(comptime value: Word) returns (comptime<Word>) {",
  "  return right(value);",
  "}",
  "function right(comptime value: Word) returns (comptime<Word>) {",
  "  return left(value);",
  "}",
  "function entry() returns (Word) { return left(1); }"
]

private def eagerRecursiveSource : String := String.intercalate "\n" [
  "function constant(comptime value: Word) returns (comptime<Word>) {",
  "  return value;",
  "}",
  "function loop(comptime value: Word) returns (comptime<Word>) {",
  "  return loop(value);",
  "}",
  "function entry() returns (Word) {",
  "  return true ? constant(1) : loop(0);",
  "}"
]

private def testRecursiveRejections : IO Unit := do
  expectRecursiveCall "self recursion" selfRecursiveSource "entry" 2
  expectRecursiveCall "mutual recursion" mutualRecursiveSource "entry" 3
  expectRecursiveCall "eager unselected recursion" eagerRecursiveSource
    "entry" 3

private def deepAcyclicSource : String := String.intercalate "\n" [
  "function leaf(comptime value: Word) returns (comptime<Word>) {",
  "  return value + 1;",
  "}",
  "function stepOne(value: Word) returns (comptime<Word>) {",
  "  return leaf(value) + 1;",
  "}",
  "function stepTwo(value: Word) returns (comptime<Word>) {",
  "  return stepOne(value) + 1;",
  "}",
  "function stepThree(value: Word) returns (comptime<Word>) {",
  "  return stepTwo(value) + 1;",
  "}",
  "function entry() returns (Word) { return stepThree(5); }"
]

private def testDeepAcyclicCall : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace deepAcyclicSource)
      (Seed.named moduleId "entry") (limits 5) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"deep acyclic staged calls failed with sufficient budget: {reprStr error}")
  let expectedWord := word 9
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expectedWord ∧
      prepared.entry.elaborated.core = .word expectedWord))
    "deep acyclic staged chain was not reified as one closed Word"
  let store : Core.Store := [.bool true, .word (word 37)]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (.word expectedWord) store)))
    "deep acyclic staged chain changed its value or store"

private def ordinaryEvidenceLetSource : String := String.intercalate "\n" [
  "trait Coerce<From, To> {",
  "  function coerce(value: From) returns (To);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(value: Bool) returns (Word) { return 91; }",
  "}",
  "function entry() returns (Word) {",
  "  let alias: Word = true;",
  "  return alias;",
  "}"
]

private def testOrdinaryEvidenceLetPreserved : IO Unit := do
  let moduleId ← mainModule
  let prepared ← match prepare (workspace ordinaryEvidenceLetSource)
      (Seed.named moduleId "entry") (limits 1) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"ordinary evidence-bearing let regressed: {reprStr error}")
  assertTrue (decide (prepared.run? [] 4096 =
      some (.done (.word (word 91)) [])))
    "general staged caching bypassed ordinary coercion evidence execution"

private def comptimeInputDraftSource : String := String.intercalate "\n" [
  "function staged() returns (comptime<Word>) { return 7; }",
  "function helper(comptime unused: Word) returns (Word) {",
  "  return staged();",
  "}",
  "function entry() returns (Word) { return helper(1); }"
]

private def testComptimeInputDraftBoundary : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace comptimeInputDraftSource)
      (Seed.named moduleId "entry") (limits 3) with
  | .error (.linking (.runtimeCallComptimeResult _ _ _)) => pure ()
  | result => throw (IO.userError
      s!"comptime-input runtime draft crossed the documented phase boundary: {reprStr result}")

/-- Fix unsupported evidence/coercion boundaries, eager recursion rejection,
ordinary evidence-let compatibility, the comptime-input draft boundary, and
successful finite evaluation of a sufficiently budgeted acyclic chain. -/
def testSourceStagedValueCallsTamper : IO Unit := do
  testPredicateRejected
  testResultCoercionRejected
  testRecursiveRejections
  testDeepAcyclicCall
  testOrdinaryEvidenceLetPreserved
  testComptimeInputDraftBoundary

end Tests.SourceStagedValueCallsTamper
