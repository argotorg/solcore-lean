import Solcore

/-!
Whole-program regressions for Core-representable staged-value calls.

These cases enter only through the public source-program preparation and
execution boundary.  A successful case therefore checks source typing,
specialization discovery, direct linking, staged evaluation, Core reification,
and runtime execution together.
-/

set_option autoImplicit false

namespace Tests.SourceStagedValueCalls

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
  | none => throw (IO.userError "invalid staged-value call module path")
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

private def positiveSource : String := String.intercalate "\n" [
  "function bump(comptime value: Word) returns (comptime<Word>) {",
  "  let alias: Word = (value);",
  "  return alias + 1;",
  "}",
  "function negate(comptime flag: Bool) returns (comptime<Bool>) {",
  "  return !flag;",
  "}",
  "function stagedUnit() returns (comptime<()>) { return; }",
  "function bundle(comptime value: Word, comptime flag: Bool) returns (comptime<(Word, Bool, ())>) {",
  "  let next: Word = bump(value);",
  "  return (next, negate(flag), stagedUnit());",
  "}",
  "function relay(value: Word) returns (comptime<Word>) {",
  "  let alias: Word = bump(value);",
  "  return bump(alias);",
  "}",
  "function entryWord() returns (Word) { return bump(41); }",
  "function entryBool() returns (Bool) { return negate(false); }",
  "function entryUnit() returns (()) { return stagedUnit(); }",
  "function entryProduct() returns ((Word, Bool, ())) {",
  "  return bundle(6, true);",
  "}",
  "function entryNested() returns (Word) { return relay(5); }",
  "function entryResultAlias() returns (Word) {",
  "  let alias: Word = relay(5);",
  "  return alias;",
  "}",
  "function entryAlias() returns (Word) {",
  "  let closed: Word = 8;",
  "  return relay(closed);",
  "}"
]

private def prepareNamed (content name : String) (budget : Nat) :
    IO PreparedEntry := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId name) (limits budget) with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError
      s!"{name}: staged-value call preparation failed: {reprStr error}")

private def assertPreparedClosed (name : String)
    (expected : SourceStagedValue.Value) : IO Unit := do
  let prepared ← prepareNamed positiveSource name 8
  let expectedValue := SourceStagedValue.toCore expected
  let expectedResolved := SourceStagedValue.toResolved expected
  let expectedCore := SourceStagedValue.toCoreExpr expected
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = expectedResolved ∧
      prepared.entry.elaborated.core = expectedCore))
    s!"{name}: marked result was not reified as the exact closed Core value"
  let store : Core.Store := [
    .bool false,
    .word (word 77),
    .pair (.word (word 3)) (.bool true)
  ]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done expectedValue store)))
    s!"{name}: prepared execution changed its value or store"
  let moduleId ← mainModule
  match SourceProgramExecution.run (workspace positiveSource)
      (Seed.named moduleId name) [] (limits 8) store with
  | .ok result =>
      assertTrue (decide (result = .done expectedValue store))
        s!"{name}: public run disagreed with the prepared entry"
  | .error error => throw (IO.userError
      s!"{name}: public staged-value execution failed: {reprStr error}")

private def testClosedResults : IO Unit := do
  assertPreparedClosed "entryWord" (.word (word 42))
  assertPreparedClosed "entryBool" (.bool true)
  assertPreparedClosed "entryUnit" .unit
  assertPreparedClosed "entryProduct"
    (.product (.word (word 7)) (.product (.bool false) .unit))
  assertPreparedClosed "entryNested" (.word (word 7))

private def testRuntimeCallerAlias : IO Unit := do
  let resultAlias ← prepareNamed positiveSource "entryResultAlias" 8
  let seven := word 7
  match resultAlias.entry.elaborated.resolved with
  | .letE binder (.word value) (.var reference) =>
      assertTrue (decide (binder = reference ∧ value = seven))
        "runtime result alias did not retain a closed staged initializer"
  | resolved => throw (IO.userError
      s!"runtime result alias has the wrong resolved shape: {reprStr resolved}")
  assertTrue (decide (resultAlias.run? [] 4096 =
      some (.done (.word seven) [])))
    "runtime result alias did not execute to the staged value"

  let prepared ← prepareNamed positiveSource "entryAlias" 8
  let expected := Core.Value.word (word 10)
  let store : Core.Store := [.word (word 91), .bool true]
  assertTrue (prepared.inputTypes.isEmpty)
    "entryAlias unexpectedly retained a runtime input"
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done expected store)))
    "a comptime-classified caller let alias did not cross nested marked calls"
  let moduleId ← mainModule
  match SourceProgramExecution.run (workspace positiveSource)
      (Seed.named moduleId "entryAlias") [] (limits 8) store with
  | .ok result =>
      assertTrue (decide (result = .done expected store))
        "public execution changed the caller-alias result"
  | .error error => throw (IO.userError
      s!"entryAlias: public execution failed: {reprStr error}")

private def boundarySource : String := String.intercalate "\n" [
  "function identity(comptime value: Word) returns (comptime<Word>) {",
  "  return value;",
  "}",
  "function producer(value: Word) returns (Word) { return value; }",
  "function runtimeAlias(value: Word) returns (Word) {",
  "  let alias: Word = value;",
  "  return identity(alias);",
  "}",
  "function deferredAlias(value: Word) returns (Word) {",
  "  let alias: Word = producer(value);",
  "  return identity(alias);",
  "}"
]

private def testRuntimeArgumentRejected : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace boundarySource)
      (Seed.named moduleId "runtimeAlias") (limits 3) with
  | .error (.linking (.runtimeArgumentToComptimeParameter _ _ 0 _)) =>
      pure ()
  | result => throw (IO.userError
      s!"runtime-dependent alias crossed a comptime parameter: {reprStr result}")

private def testDeferredArgumentRejected : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace boundarySource)
      (Seed.named moduleId "deferredAlias") (limits 4) with
  | .error (.linking (.comptimeArgumentDeferred _ _ 0 _)) => pure ()
  | result => throw (IO.userError
      s!"deferred alias crossed a comptime parameter: {reprStr result}")

/-- Exercise general staged direct calls through the public source-program
pipeline, including nested calls and caller-local stage propagation. -/
def testSourceStagedValueCalls : IO Unit := do
  testClosedResults
  testRuntimeCallerAlias
  testRuntimeArgumentRejected
  testDeferredArgumentRejected

end Tests.SourceStagedValueCalls
