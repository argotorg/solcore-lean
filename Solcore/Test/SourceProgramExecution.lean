import Solcore

/-! End-to-end regressions for the explicit public source execution pipeline. -/

set_option autoImplicit false

namespace Tests.SourceProgramExecution

open Solcore Solcore.Frontend Solcore.Frontend.SourceProgramExecution
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  ⟨value % Core.wordModulus, Nat.mod_lt _ (by simp [Core.wordModulus])⟩

private def mainModule (path : String) : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse path with
  | none => throw (IO.userError s!"invalid test module path `{path}`")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def rawWorkspace (entry : String)
    (sources : List (String × String)) : Workspace.RawWorkspace := {
  entry
  mainSources := sources.map fun source => {
    path := source.1
    content := source.2
  }
  externalLibraries := []
}

private def basicSource : String := String.intercalate "\n" [
  "function identity<T>(value: T) returns (T) { return value; }",
  "function entry(value: Word, flag: Bool) returns (Word) {",
  "  return flag ? identity(value) : 7;",
  "}"
]

private def basicWorkspace : Workspace.RawWorkspace :=
  rawWorkspace "main.solc" [("main.solc", basicSource)]

private def generousLimits : Limits := {
  checkingFuel := 1024
  specializationBudget := 8
  executionFuel := 4096
}

private def testNamedSeedAndPreparedRun : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let seed := Seed.named moduleId "entry"
  let prepared ← match prepare basicWorkspace seed generousLimits with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError
        s!"named root preparation failed: {reprStr error}")
  assertTrue (decide (prepared.key.declaration.moduleId = moduleId ∧
      prepared.key.declaration.declarationIndex = 1 ∧
      prepared.key.arguments = [] ∧
      prepared.inputTypes = [.word, .bool]))
    "named root did not retain its explicit module, declaration, or inputs"
  let fortyOne : Core.Value := .word (word 41)
  assertTrue (decide (prepared.run? [fortyOne, .bool true] 4096 =
      some (.done fortyOne [])))
    "prepared named root did not execute its reachable generic call"
  assertTrue (decide (prepared.run? [fortyOne, .bool false] 4096 =
      some (.done (.word (word 7)) [])))
    "prepared named root did not execute its other conditional branch"
  assertTrue ((prepared.run? [.bool true, fortyOne] 4096).isNone)
    "prepared run? accepted runtime values in the wrong type order"

private def testDeclarationSeedAndStore : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let declaration : Resolved.DeclarationId := {
    moduleId
    declarationIndex := 0
  }
  let seed := Seed.declaration declaration [.word]
  let input : Core.Value := .word (word 19)
  let store : Core.Store := [.bool false, .word (word 3)]
  match run basicWorkspace seed [input] generousLimits store with
  | .ok result =>
      assertTrue (decide (result = .done input store))
        "declaration root lost its generic argument, input, or supplied store"
  | .error error => throw (IO.userError
      s!"declaration root execution failed: {reprStr error}")

private def testModuleQualifiedName : IO Unit := do
  let mainId ← mainModule "main.solc"
  let otherId ← mainModule "other.solc"
  let workspace := rawWorkspace "main.solc" [
    ("main.solc", "function entry() returns (Word) { return 11; }"),
    ("other.solc", "function entry() returns (Word) { return 22; }")
  ]
  match run workspace (Seed.named otherId "entry") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 22)) []))
        "module-qualified seed followed the raw workspace entry instead"
  | .error error => throw (IO.userError
      s!"module-qualified root failed: {reprStr error}")
  match run workspace (Seed.named mainId "entry") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 11)) []))
        "explicit main-module seed selected another module"
  | .error error => throw (IO.userError
      s!"main-module root failed: {reprStr error}")

private def testDeferredIntegerOperators : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let workspace := rawWorkspace "main.solc" [("main.solc",
    String.intercalate "\n" [
      "function accept(value: Word) returns (Word) { return value; }",
      "function nestedAdd() returns (Word) { return accept(1 + 1); }",
      "function nestedNot() returns (Word) { return accept(~1); }"
    ])]
  match run workspace (Seed.named moduleId "nestedAdd") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 2)) []))
        "public execution changed deferred nested addition"
  | .error error => throw (IO.userError
      s!"public deferred addition failed: {reprStr error}")
  match run workspace (Seed.named moduleId "nestedNot") [] generousLimits with
  | .ok result =>
      assertTrue (decide (result = .done (.word (word 1).bitNot) []))
        "public execution changed deferred nested complement"
  | .error error => throw (IO.userError
      s!"public deferred complement failed: {reprStr error}")

private def testSeedErrors : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let missingModule ← mainModule "missing.solc"
  match prepare basicWorkspace (Seed.named missingModule "entry") with
  | .error (.seed (.unknownModule actual)) =>
      assertTrue (decide (actual = missingModule))
        "unknown-module error changed its exact module"
  | result => throw (IO.userError
      s!"unknown seed module was accepted: {reprStr result}")
  match prepare basicWorkspace (Seed.named moduleId "absent") with
  | .error (.seed (.unknownName actual name)) =>
      assertTrue (decide (actual = moduleId ∧ name = "absent"))
        "unknown-name error changed its module or spelling"
  | result => throw (IO.userError
      s!"unknown root name was accepted: {reprStr result}")
  let identity : Resolved.DeclarationId := {
    moduleId
    declarationIndex := 0
  }
  match prepare basicWorkspace (Seed.declaration identity) with
  | .error (.seed (.typeArgumentArityMismatch actual expected supplied)) =>
      assertTrue (decide (actual = identity ∧ expected = 1 ∧ supplied = 0))
        "generic-arity error lost its declaration or counts"
  | result => throw (IO.userError
      s!"missing generic type argument was accepted: {reprStr result}")
  let openArgument : Ty := .variable ⟨77⟩
  match prepare basicWorkspace
      (Seed.declaration identity [openArgument]) generousLimits with
  | .error (.worklist (.specialization actual
        (.nonConcreteArgument _ (.flexible variableId)))) =>
      assertTrue (decide (actual = identity ∧ variableId = ⟨77⟩))
        "open generic argument lost its worklist-stage rejection"
  | result => throw (IO.userError
      s!"open generic type argument was accepted: {reprStr result}")
  let missing : Resolved.DeclarationId := {
    moduleId
    declarationIndex := 99
  }
  match prepare basicWorkspace (Seed.declaration missing) with
  | .error (.seed (.unknownDeclaration actual)) =>
      assertTrue (decide (actual = missing))
        "unknown-declaration error changed its identity"
  | result => throw (IO.userError
      s!"unknown declaration root was accepted: {reprStr result}")

private def testAmbiguousAndNonFunctionSeeds : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let overloaded := rawWorkspace "main.solc" [("main.solc",
    String.intercalate "\n" [
      "function choose(value: Word) returns (Word) { return value; }",
      "function choose(value: Bool) returns (Bool) { return value; }"
    ])]
  match prepare overloaded (Seed.named moduleId "choose") with
  | .error (.seed (.ambiguousName actual name candidates)) =>
      assertTrue (decide (actual = moduleId ∧ name = "choose" ∧
          candidates.map (·.declarationIndex) = [0, 1]))
        "ambiguous name did not retain its ordered overload declarations"
  | result => throw (IO.userError
      s!"ambiguous root name was accepted: {reprStr result}")
  let traitWorkspace := rawWorkspace "main.solc" [("main.solc",
    String.intercalate "\n" [
      "trait Marker<T> {}",
      "function entry() returns (Word) { return 1; }"
    ])]
  let traitId : Resolved.DeclarationId := {
    moduleId
    declarationIndex := 0
  }
  match prepare traitWorkspace (Seed.declaration traitId [.word]) with
  | .error (.seed (.declarationNotFunction actual .trait)) =>
      assertTrue (decide (actual = traitId))
        "non-function seed error changed its declaration"
  | result => throw (IO.userError
      s!"trait declaration was accepted as an execution root: {reprStr result}")

private def testStageErrors : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let malformed := rawWorkspace "main.solc" [("main.solc",
    "function broken(value: Missing) returns (Word) { return 1; }")]
  match prepare malformed (Seed.named moduleId "broken") with
  | .error (.checking (_ :: _)) => pure ()
  | result => throw (IO.userError
      s!"checking failure lost its pipeline stage: {reprStr result}")
  let noChecking : Limits := {
    checkingFuel := 0
    specializationBudget := 8
    executionFuel := 4096
  }
  match prepare basicWorkspace (Seed.named moduleId "entry") noChecking with
  | .error (.checking (_ :: _)) => pure ()
  | result => throw (IO.userError
      s!"checking fuel was not routed to source inference: {reprStr result}")
  let tight : Limits := {
    checkingFuel := 1024
    specializationBudget := 1
    executionFuel := 4096
  }
  match prepare basicWorkspace (Seed.named moduleId "entry") tight with
  | .error (.specializationBudgetExhausted next pendingCount) =>
      assertTrue (decide (next.declaration.moduleId = moduleId ∧
          next.declaration.declarationIndex = 0 ∧
          next.arguments = [.word] ∧ pendingCount = 1))
        "specialization frontier lost its exact next key or queue size"
  | result => throw (IO.userError
      s!"specialization exhaustion lost its public stage: {reprStr result}")
  let indirect := rawWorkspace "main.solc" [("main.solc",
    "function apply(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }")]
  match prepare indirect (Seed.named moduleId "apply") generousLimits with
  | .ok prepared =>
      let identity : Core.Value := .closure .word .word (.var 0) []
      let input : Core.Value := .word (word 23)
      assertTrue (decide (prepared.inputTypes =
          [.function .word .word, .word] ∧
          prepared.run? [identity, input] 128 = some (.done input [])))
        "indirect call did not execute the supplied Core closure"
  | .error error => throw (IO.userError
      s!"indirect call was not prepared: {reprStr error}")
  let recursive := rawWorkspace "main.solc" [("main.solc",
    "function loop(value: Word) returns (Word) { return loop(value); }")]
  match prepare recursive (Seed.named moduleId "loop") generousLimits with
  | .ok prepared =>
      let input : Core.Value := .word (word 1)
      match prepared.run? [input] 16 with
      | some (.outOfFuel _) => pure ()
      | result => throw (IO.userError
          s!"recursive source root did not exhaust runtime fuel: {reprStr result}")
  | .error error => throw (IO.userError
      s!"recursive source root was not prepared: {reprStr error}")

private def testRuntimeBoundary : IO Unit := do
  let moduleId ← mainModule "main.solc"
  let seed := Seed.named moduleId "entry"
  match run basicWorkspace seed [.bool true, .bool false] generousLimits with
  | .error (.inputTypesMismatch expected actual) =>
      assertTrue (decide (expected = [.word, .bool] ∧
          actual = [.bool, .bool]))
        "runtime input mismatch lost its exact expected or actual types"
  | result => throw (IO.userError
      s!"ill-typed runtime inputs crossed the public pipeline: {reprStr result}")
  let noExecution : Limits := {
    generousLimits with executionFuel := 0
  }
  match run basicWorkspace seed [.word (word 41), .bool true] noExecution with
  | .ok (.outOfFuel _) => pure ()
  | result => throw (IO.userError
      s!"Core fuel exhaustion became a pipeline error: {reprStr result}")

/-- Exercise both explicit seed forms, all public stages, and runtime policy. -/
def testSourceProgramExecution : IO Unit := do
  testNamedSeedAndPreparedRun
  testDeclarationSeedAndStore
  testModuleQualifiedName
  testDeferredIntegerOperators
  testSeedErrors
  testAmbiguousAndNonFunctionSeeds
  testStageErrors
  testRuntimeBoundary
  IO.println "explicit raw-source check/specialize/link/run pipeline GREEN"

end Tests.SourceProgramExecution
