import Solcore

/-!
End-to-end regressions for evidence-selected unary and binary operations in the
Core-representable staged-value domain.
-/

set_option autoImplicit false

namespace Tests.SourceStagedRequiredOperators

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
  | none => throw (IO.userError "invalid staged required-operator module path")
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

private def prepareNamed (content name : String) : IO PreparedEntry := do
  let moduleId ← mainModule
  match prepare (workspace content) (Seed.named moduleId name) limits with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError
      s!"{name}: staged required-operator preparation failed: {reprStr error}")

private def assertClosedResult (content name : String)
    (expected : SourceStagedValue.Value) : IO Unit := do
  let prepared ← prepareNamed content name
  assertTrue (decide (prepared.inputTypes = [] ∧
      prepared.entry.elaborated.resolved =
        SourceStagedValue.toResolved expected ∧
      prepared.entry.elaborated.core = SourceStagedValue.toCoreExpr expected))
    s!"{name}: staged required operation was not materialized exactly"
  let store : Core.Store := [
    .bool true,
    .word (word 73),
    .pair (.word (word 4)) (.bool false)
  ]
  assertTrue (decide (prepared.run? [] 4096 store =
      some (.done (SourceStagedValue.toCore expected) store)))
    s!"{name}: staged required operation changed its result or store"

private def evidenceSource : String := String.intercalate "\n" [
  "trait Eq<T> {",
  "  function eq(left: T, right: T) returns (Bool);",
  "}",
  "trait Add<T> {",
  "  function add(left: T, right: T) returns (T) where T: Eq;",
  "}",
  "trait BitNot<T> {",
  "  function bnot(value: T) returns (T);",
  "}",
  "impl Eq<Word> {",
  "  function eq(left: Word, right: Word) returns (Bool) { return false; }",
  "}",
  "function equalWithEvidence<T>(left: T, right: T) returns (Bool)",
  "    where T: Eq {",
  "  return left == right;",
  "}",
  "impl Add<Word> {",
  "  function add(left: Word, right: Word) returns (Word) where Word: Eq {",
  "    return equalWithEvidence(left, right) ? 91 : 92;",
  "  }",
  "}",
  "impl BitNot<Word> {",
  "  function bnot(value: Word) returns (Word) { return 94; }",
  "}",
  "function stagedAdd<T>(comptime left: T, comptime right: T)",
  "    returns (comptime<T>) where T: Add, T: Eq {",
  "  return left + right;",
  "}",
  "function relayAdd<T>(comptime left: T, comptime right: T)",
  "    returns (comptime<T>) where T: Add, T: Eq {",
  "  return stagedAdd(left, right);",
  "}",
  "function stagedBitNot<T>(comptime value: T) returns (comptime<T>)",
  "    where T: BitNot {",
  "  return ~value;",
  "}",
  "function addEntry() returns (Word) { return relayAdd(5, 5); }",
  "function bitNotEntry() returns (Word) { return stagedBitNot(7); }"
]

private def testSelectedImplementationMethods : IO Unit := do
  assertClosedResult evidenceSource "addEntry" (.word (word 92))
  assertClosedResult evidenceSource "bitNotEntry" (.word (word 94))

private def builtinSource : String := String.intercalate "\n" [
  "function builtins(comptime left: Word, comptime right: Word)",
  "    returns (comptime<(Word, Word)>) {",
  "  return (left + right, ~left);",
  "}",
  "function builtinEntry() returns ((Word, Word)) {",
  "  return builtins(5, 6);",
  "}"
]

private def testRequirementFreeBuiltinCompatibility : IO Unit := do
  assertClosedResult builtinSource "builtinEntry"
    (.product (.word (word 11)) (.word (word 5).bitNot))

def testSourceStagedRequiredOperators : IO Unit := do
  testSelectedImplementationMethods
  testRequirementFreeBuiltinCompatibility

end Tests.SourceStagedRequiredOperators
