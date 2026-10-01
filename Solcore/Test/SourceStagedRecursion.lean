import Solcore
import Solcore.Test.SourceCompilerFeatureSupport

/-!
End-to-end regressions for fuel-bounded, selected-branch staged recursion.

These tests exercise both the dedicated staged-integer evaluator and the
general Core-representable staged-value evaluator through the public program
preparation boundary.  Successful cases must close to constants and preserve
the caller's store; divergent staged calls and ordinary runtime recursion keep
distinct errors. Runtime recursion uses the common public Core compiler and
a typed checkpoint; staging and runtime keep separate execution budgets.
-/

set_option autoImplicit false

namespace Tests.SourceStagedRecursion

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
  | none => throw (IO.userError "invalid staged-recursion module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def limits (specializationBudget stagingFuel : Nat) : Limits := {
  checkingFuel := 4096
  specializationBudget
  stagingFuel
  executionFuel := 4096
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def prepareNamed (label content root : String)
    (specializationBudget stagingFuel : Nat) : IO PreparedEntry := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId root)
      (limits specializationBudget stagingFuel) with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError
      s!"{label}: staged-recursion preparation failed: {reprStr error}")

private def preservedStore : Core.Store := [
  .bool false,
  .word (word 73),
  .pair (.word (word 4)) (.bool true)
]

private def assertClosedWord (label content root : String)
    (specializationBudget stagingFuel expected : Nat) : IO Unit := do
  let prepared ← prepareNamed label content root specializationBudget stagingFuel
  let expectedWord := word expected
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word expectedWord ∧
      prepared.entry.elaborated.core = .word expectedWord))
    s!"{label}: staged recursion was not materialized as one Word constant"
  assertTrue (decide (prepared.run? [] 4096 preservedStore =
      some (.done (.word expectedWord) preservedStore)))
    s!"{label}: staged recursion changed its result or caller store"

private def assertClosedBool (label content root : String)
    (specializationBudget stagingFuel : Nat) (expected : Bool) : IO Unit := do
  let prepared ← prepareNamed label content root specializationBudget stagingFuel
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .bool expected ∧
      prepared.entry.elaborated.core = .bool expected))
    s!"{label}: staged recursion was not materialized as one Bool constant"
  assertTrue (decide (prepared.run? [] 4096 preservedStore =
      some (.done (.bool expected) preservedStore)))
    s!"{label}: staged recursion changed its result or caller store"

private def integerRecursionSource : String := String.intercalate "\n" [
  "function countdown(comptime n: integer) returns (comptime<integer>) {",
  "  return integerEq(n, 0) ? 0 : countdown(integerSub(n, 1));",
  "}",
  "function factorial(comptime n: integer) returns (comptime<integer>) {",
  "  return integerEq(n, 0) ? 1 :",
  "    integerMul(n, factorial(integerSub(n, 1)));",
  "}",
  "function fib(comptime n: integer) returns (comptime<integer>) {",
  "  return integerLt(n, 2) ? n :",
  "    integerAdd(fib(integerSub(n, 1)), fib(integerSub(n, 2)));",
  "}",
  "function left(comptime n: integer) returns (comptime<integer>) {",
  "  return integerEq(n, 0) ? 0 : right(integerSub(n, 1));",
  "}",
  "function right(comptime n: integer) returns (comptime<integer>) {",
  "  return integerEq(n, 0) ? 0 : left(integerSub(n, 1));",
  "}",
  "function countdownEntry() returns (Word) {",
  "  return wordFromInteger(countdown(5));",
  "}",
  "function factorialEntry() returns (Word) {",
  "  return wordFromInteger(factorial(5));",
  "}",
  "function fibEntry() returns (Word) {",
  "  return wordFromInteger(fib(10));",
  "}",
  "function mutualEntry() returns (Word) {",
  "  return wordFromInteger(left(6));",
  "}"
]

private def testIntegerRecursion : IO Unit := do
  assertClosedWord "integer countdown" integerRecursionSource
    "countdownEntry" 2 64 0
  assertClosedWord "integer factorial" integerRecursionSource
    "factorialEntry" 2 64 120
  assertClosedWord "integer Fibonacci" integerRecursionSource
    "fibEntry" 2 64 55
  assertClosedWord "integer mutual countdown" integerRecursionSource
    "mutualEntry" 3 64 0

private def generalRecursionSource : String := String.intercalate "\n" [
  "function finishWord(comptime value: Word, comptime stop: Bool)",
  "    returns (comptime<Word>) {",
  "  return stop ? value : finishWord(value, true);",
  "}",
  "function finishBool(comptime stop: Bool) returns (comptime<Bool>) {",
  "  return stop ? true : finishBool(true);",
  "}",
  "function finishStatement(comptime stop: Bool) returns (comptime<Word>) {",
  "  if (stop) {",
  "    return 9;",
  "  } else {",
  "    return finishStatement(true);",
  "  }",
  "}",
  "function wordEntry() returns (Word) {",
  "  return finishWord(7, false);",
  "}",
  "function boolEntry() returns (Bool) {",
  "  return finishBool(false);",
  "}",
  "function statementEntry() returns (Word) {",
  "  return finishStatement(false);",
  "}"
]

private def testGeneralWordAndBoolRecursion : IO Unit := do
  assertClosedWord "general Word/Bool recursion" generalRecursionSource
    "wordEntry" 2 16 7
  assertClosedBool "general Bool recursion" generalRecursionSource
    "boolEntry" 2 16 true
  assertClosedWord "general statement recursion" generalRecursionSource
    "statementEntry" 2 16 9

private def genericEvidenceRecursionSource : String := String.intercalate "\n" [
  "trait Marker<T> {}",
  "impl Marker<Word> {}",
  "function finish<T>(comptime value: T, comptime stop: Bool)",
  "    returns (comptime<T>) where T: Marker {",
  "  return stop ? value : finish(value, true);",
  "}",
  "function entry() returns (Word) { return finish(11, false); }"
]

private def testGenericEvidenceRecursion : IO Unit :=
  assertClosedWord "generic evidence recursion" genericEvidenceRecursionSource
    "entry" 2 16 11

private def unselectedFaultSource : String := String.intercalate "\n" [
  "function safe() returns (comptime<Word>) {",
  "  return true ? 7 : 1 / 0;",
  "}",
  "function entry() returns (Word) { return safe(); }"
]

private def testUnselectedFaultIsNotExecuted : IO Unit :=
  assertClosedWord "unselected staged fault" unselectedFaultSource
    "entry" 2 8 7

private def unselectedRecursiveBranchSource : String :=
  String.intercalate "\n" [
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

private def testUnselectedInfiniteRecursionIsNotExecuted : IO Unit :=
  assertClosedWord "unselected infinite recursion"
    unselectedRecursiveBranchSource "entry" 3 8 1

private def expectStagedInvocationCycle (label content root : String)
    (specializationBudget stagingFuel : Nat) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId root)
      (limits specializationBudget stagingFuel) with
  | .error (.linking (.stagedInvocationCycle _)) => pure ()
  | result => throw (IO.userError
      s!"{label}: expected a staged invocation cycle, got {reprStr result}")

private def selfCycleSource : String := String.intercalate "\n" [
  "function loop(comptime n: integer) returns (comptime<integer>) {",
  "  return loop(n);",
  "}",
  "function entry() returns (Word) { return wordFromInteger(loop(1)); }"
]

private def mutualCycleSource : String := String.intercalate "\n" [
  "function left(comptime value: Word) returns (comptime<Word>) {",
  "  return right(value);",
  "}",
  "function right(comptime value: Word) returns (comptime<Word>) {",
  "  return left(value);",
  "}",
  "function entry() returns (Word) { return left(1); }"
]

private def testSameValueCycles : IO Unit := do
  expectStagedInvocationCycle "same-value self recursion" selfCycleSource
    "entry" 2 16
  expectStagedInvocationCycle "same-value mutual recursion" mutualCycleSource
    "entry" 3 16

private def expectStagedFuelExhausted (label content root : String)
    (specializationBudget stagingFuel : Nat) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId root)
      (limits specializationBudget stagingFuel) with
  | .error (.linking (.stagedFuelExhausted _)) => pure ()
  | result => throw (IO.userError
      s!"{label}: expected staged fuel exhaustion, got {reprStr result}")

private def increasingSource : String := String.intercalate "\n" [
  "function grow(comptime n: integer) returns (comptime<integer>) {",
  "  return grow(integerAdd(n, 1));",
  "}",
  "function entry() returns (Word) { return wordFromInteger(grow(0)); }"
]

private def testStagedFuelBoundaries : IO Unit := do
  expectStagedFuelExhausted "increasing staged nontermination"
    increasingSource "entry" 2 8
  expectStagedFuelExhausted "terminating recursion with insufficient fuel"
    integerRecursionSource "countdownEntry" 2 1

private def runtimeRecursionSource : String := String.intercalate "\n" [
  "function loop(value: Word) returns (Word) { return loop(value); }"
]

private def testRuntimeRecursionUsesExecutionFuel : IO Unit := do
  let moduleId ← mainModule
  let source ← SourceCompilerFeatureSupport.get "runtime recursion compilation"
    (SourceCoreCompiler.compile (workspace runtimeRecursionSource)
      [SourceCoreCompiler.Seed.named moduleId "loop"]
      {checkingFuel := 4096, specializationBudget := 1, compilationFuel := 1000})
  assertTrue (source.rootCount == 1 && source.plan.specializations.length == 1)
    "runtime recursion did not retain one Core specialization"
  let compiled ← SourceCompilerFeatureSupport.fromCompiled source
  let invoked ← compiled.invoke [.word (word 1)] {inputValidationFuel := 64, executionFuel := 200}
  match invoked.outcome with
  | .outOfFuel checkpoint =>
      assertTrue (checkpoint.heapSize > invoked.initial.heapSize)
        "runtime recursion did not retain its allocated parameter cells"
      match ← checkpoint.resume 200 with
      | .outOfFuel continued =>
          assertTrue (continued.heapSize ≥ checkpoint.heapSize)
            "resumed runtime recursion discarded allocated cells"
      | _ => throw (IO.userError "resumed runtime recursion unexpectedly terminated")
  | _ => throw (IO.userError "runtime recursion did not use the execution fuel boundary")

/-- Exercise staged and Core runtime recursion through their
independent public fuel boundaries. -/
def testSourceStagedRecursion : IO Unit := do
  testIntegerRecursion
  testGeneralWordAndBoolRecursion
  testGenericEvidenceRecursion
  testUnselectedFaultIsNotExecuted
  testUnselectedInfiniteRecursionIsNotExecuted
  testSameValueCycles
  testStagedFuelBoundaries
  testRuntimeRecursionUsesExecutionFuel
  IO.println "staged recursion checks GREEN"

end Tests.SourceStagedRecursion
