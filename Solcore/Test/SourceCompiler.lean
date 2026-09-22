import Solcore

/-! End-to-end regressions for the phase-9 public source compiler boundary. -/

set_option autoImplicit false

namespace Tests.SourceCompiler

open Solcore Solcore.Frontend Solcore.TypeSystem
open Solcore.Frontend.SourceCompiler

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def moduleId (path : String) : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse path with
  | none => throw (IO.userError s!"invalid test module path `{path}`")
  | some canonical => pure {
      library := .main
      path := canonical.modulePath
    }

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    {
      path := "main.solc"
      content := String.intercalate "\n" [
        "import {Ticket, WordTicket} from provider;",
        "function direct(value: Word) returns (Word) { return value * 2; }",
        "function recurse(value: Word) returns (Word) {",
        "  return value == 0 ? 31 : recurse(value - 1);",
        "}",
        "function visibleAlias(value: Word) returns (Word) {",
        "  let ticket: WordTicket = .Open(value);",
        "  match (ticket) {",
        "    case .Open(inner) {",
        "      let result: Word = inner;",
        "      result += 5;",
        "      return result;",
        "    }",
        "    default { return 0; }",
        "  }",
        "}"
      ]
    },
    {
      path := "provider.solc"
      content := String.intercalate "\n" [
        "enum Ticket<T> { Open(T), Closed }",
        "type WordTicket = Ticket<Word>;",
        "export {Ticket(Open), WordTicket};"
      ]
    },
    {
      path := "blocked.solc"
      content := String.intercalate "\n" [
        "trait Coerce<From, To> {}",
        "enum Box { Only }",
        "impl Coerce<Word, Box> {}",
        "function accept(value: Box) returns (Box) { return value; }",
        "function blocked(value: Word) returns (Box) { return accept(value); }"
      ]
    }
  ]
  externalLibraries := []
}

private def compilerOptions : CompileOptions := {
  specializationBudget := 32
  stagingFuel := 128
}

private def runtimeOptions : RunOptions := {
  inputValidationFuel := 64
  executionFuel := 4096
}

private def checkedWorkspace : IO CheckedProgram := do
  match checkProgram workspace with
  | .ok checked => pure checked
  | .error errors => throw (IO.userError
      s!"compiler fixture failed checking: {reprStr errors}")

private def compileNamed (checked : CheckedProgram) (path name : String) :
    IO CompiledEntry := do
  let selectedModule ← moduleId path
  match compileChecked checked (Seed.named selectedModule name) compilerOptions with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError
      s!"`{path}.{name}` failed compilation: {reprStr error}")

private def expectCoreWord (label : String) (expected : Nat) :
    Except RunError ExecutionResult → IO Unit
  | .ok (.core (.done (.word actual) [])) =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def expectGraphWord (label : String) (expected : Nat) :
    Except RunError ExecutionResult → IO Unit
  | .ok (.callGraph (.done (.word actual) [])) =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private def expectTypedWord (label : String) (expected : Nat) :
    Except RunError ExecutionResult → IO Unit
  | .ok (.typedSource (.done (.word actual) _)) =>
      assertTrue (actual == word expected) s!"{label} returned the wrong Word"
  | result => throw (IO.userError s!"{label} returned {reprStr result}")

private structure PreparedSet where
  checked : CheckedProgram
  direct : CompiledEntry
  recursive : CompiledEntry
  typed : CompiledEntry

private def testCheckedReuseAndPrecedence : IO PreparedSet := do
  let checked ← checkedWorkspace
  let direct ← compileNamed checked "main.solc" "direct"
  let recursive ← compileNamed checked "main.solc" "recurse"
  let typed ← compileNamed checked "main.solc" "visibleAlias"
  let main ← moduleId "main.solc"
  assertTrue (decide (
      direct.backend = .core ∧
      recursive.backend = .callGraph ∧
      typed.backend = .typedSource))
    "automatic backend precedence changed"
  assertTrue (decide (
      direct.key.declaration.moduleId = main ∧
      recursive.key.declaration.moduleId = main ∧
      typed.key.declaration.moduleId = main ∧
      direct.key.arguments = [] ∧ recursive.key.arguments = [] ∧
      typed.key.arguments = []))
    "compiled roots lost their canonical module or ground arguments"
  assertTrue (decide (
      direct.inputTypes = [.word] ∧ direct.resultType = .word ∧
      recursive.inputTypes = [.word] ∧ recursive.resultType = .word ∧
      typed.inputTypes = [.word] ∧ typed.resultType = .word))
    "backend-independent source signature metadata changed"
  assertTrue (direct.specializationCount == 1 &&
      recursive.specializationCount == 1 && typed.specializationCount == 1)
    "a single-function fixture retained an unexpected specialization plan"
  expectCoreWord "direct Core root" 14 <|
    direct.runCore [.word (word 7)] runtimeOptions
  expectGraphWord "recursive graph root" 31 <|
    recursive.runCore [.word (word 3)] runtimeOptions
  expectTypedWord "imported alias typed root" 12 <|
    typed.runTyped [.word (word 7)] runtimeOptions
  pure { checked, direct, recursive, typed }

private def testTypedBoundary (prepared : PreparedSet) : IO Unit := do
  match prepared.typed.runTyped [.bool true] runtimeOptions with
  | .ok (.typedSource (.fault (.typeMismatch expected actual) state)) =>
      assertTrue (decide (expected = Ty.word ∧ actual = some Ty.bool) &&
          state.heap.isEmpty)
        "typed input rejection changed its type or mutated the heap"
  | result => throw (IO.userError
      s!"ill-typed public source input was accepted: {reprStr result}")
  let shallowExecution : RunOptions := {
    inputValidationFuel := 64
    executionFuel := 1
  }
  match prepared.typed.runTyped [.word (word 7)] shallowExecution with
  | .ok (.typedSource (.outOfFuel state)) =>
      assertTrue (state.heap.length == 1)
        "typed exhaustion did not retain the bound parameter cell"
  | result => throw (IO.userError
      s!"typed execution fuel was not independent: {reprStr result}")
  match prepared.typed.runCore [.word (word 7)] runtimeOptions with
  | .error (.invocationKindMismatch .typedSource .coreValues) => pure ()
  | result => throw (IO.userError
      s!"a Core-domain invocation crossed the typed backend: {reprStr result}")

private def testOneShotLimits : IO Unit := do
  let main ← moduleId "main.solc"
  let limits : Limits := {
    checkingFuel := 1024
    specializationBudget := 32
    stagingFuel := 128
    inputValidationFuel := 64
    executionFuel := 1
  }
  match SourceCompiler.run workspace (Seed.named main "visibleAlias")
      (Invocation.typedFresh [.word (word 7)]) limits with
  | .ok (.typedSource (.outOfFuel state)) =>
      assertTrue (state.heap.length == 1)
        "one-shot limits did not reach the selected typed runtime"
  | result => throw (IO.userError
      s!"one-shot compiler boundary returned {reprStr result}")

private def testAllBackendDiagnostics (checked : CheckedProgram) : IO Unit := do
  let blocked ← moduleId "blocked.solc"
  match compileChecked checked (Seed.named blocked "blocked") compilerOptions with
  | .error (.noBackend failures) =>
      match failures.typedSource with
      | .unsupportedExpressionCoercions _ => pure ()
      | error => throw (IO.userError
          s!"typed rejection lost its evidence diagnostic: {reprStr error}")
  | .error error => throw (IO.userError
      s!"all-backend rejection changed category: {reprStr error}")
  | .ok compiled => throw (IO.userError
      s!"an unsupported root selected {reprStr compiled.backend}")

/-- Exercise compile-once reuse, three-way selection, exact results, and
stage-preserving rejection through the public umbrella. -/
def testSourceCompiler : IO Unit := do
  let prepared ← testCheckedReuseAndPrecedence
  testTypedBoundary prepared
  testOneShotLimits
  testAllBackendDiagnostics prepared.checked
  IO.println "phase-9 public source compiler boundary GREEN"

end Tests.SourceCompiler
