import Solcore

/-!
End-to-end boundaries for implementation methods whose validated trait
contract marks parameters or results as `comptime`.
-/

set_option autoImplicit false

namespace Tests.SourceStagedMarkedImplMethods

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
  | none => throw (IO.userError "invalid staged marked-method module path")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def limits : Limits := {
  checkingFuel := 2048
  specializationBudget := 12
  executionFuel := 4096
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def source : String := String.intercalate "\n" [
  "trait Add<T> {",
  "  function add(comptime left: T, comptime right: T) returns (comptime<T>);",
  "}",
  "impl Add<Word> {",
  "  function add(comptime left: Word, comptime right: Word)",
  "      returns (comptime<Word>) {",
  "    return 94;",
  "  }",
  "}",
  "trait Coerce<From, To> {",
  "  function coerce(comptime value: From) returns (comptime<To>);",
  "}",
  "impl Coerce<Bool, Word> {",
  "  function coerce(comptime value: Bool) returns (comptime<Word>) {",
  "    return value ? 93 : 92;",
  "  }",
  "}",
  "function stagedAdd<T>(comptime left: T, comptime right: T)",
  "    returns (comptime<T>) where T: Add {",
  "  return left + right;",
  "}",
  "function stagedFlag() returns (comptime<Bool>) { return true; }",
  "function stagedAddEntry() returns (Word) { return stagedAdd(5, 6); }",
  "function stagedCoerceEntry() returns (Word) { return stagedFlag(); }",
  "function runtimeAdd<T>(left: T, right: T) returns (T) where T: Add {",
  "  return left + right;",
  "}",
  "function runtimeAddEntry(left: Word, right: Word) returns (Word) {",
  "  return runtimeAdd(left, right);",
  "}",
  "function acceptWord(value: Word) returns (Word) { return value; }",
  "function runtimeCoerceEntry(value: Bool) returns (Word) {",
  "  return acceptWord(value);",
  "}"
]

private def prepareNamed (name : String) : IO PreparedEntry := do
  let moduleId ← mainModule
  match prepare (workspace source) (Seed.named moduleId name) limits with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError
      s!"{name}: staged marked-method preparation failed: {reprStr error}")

private def assertClosedWord (name : String) (expected : Nat) : IO Unit := do
  let prepared ← prepareNamed name
  let value := word expected
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved = .word value ∧
      prepared.entry.elaborated.core = .word value))
    s!"{name}: marked implementation result was not materialized exactly"
  let store : Core.Store := [
    .bool false,
    .word (word 71),
    .pair (.word (word 4)) (.bool true)
  ]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (.word value) store)))
    s!"{name}: marked implementation changed its result or caller store"

private def testMarkedMethodsExecuteOnlyWhenStaged : IO Unit := do
  assertClosedWord "stagedAddEntry" 94
  assertClosedWord "stagedCoerceEntry" 93

private def expectRuntimeRejection (name : String)
    (expectedParameters : List Bool) : IO Unit := do
  let moduleId ← mainModule
  match prepare (workspace source) (Seed.named moduleId name) limits with
  | .error (.linking (.detachedComptimeUnsupported _ parameters true)) =>
      assertTrue (parameters == expectedParameters)
        s!"{name}: runtime rejection lost the marked parameter contract"
  | result => throw (IO.userError
      s!"{name}: a marked method escaped through runtime linking: {reprStr result}")

private def testMarkedMethodsDoNotEscapeToRuntime : IO Unit := do
  expectRuntimeRejection "runtimeAddEntry" [true, true]
  expectRuntimeRejection "runtimeCoerceEntry" [true]

def testSourceStagedMarkedImplMethods : IO Unit := do
  testMarkedMethodsExecuteOnlyWhenStaged
  testMarkedMethodsDoNotEscapeToRuntime

end Tests.SourceStagedMarkedImplMethods
