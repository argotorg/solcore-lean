import Solcore.Frontend.SourceCompiler

set_option autoImplicit false

namespace Tests.SourceCompilerFunctions

open Solcore Solcore.Frontend SourceCompiler

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function consume(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function named(value: Word) returns (Word) { return consume(inc, value); }",
    "function makeAdder(value: Word) returns (function(Word) returns (Word)) {",
    " return lam(delta: Word) -> Word { value = value + delta; return value; }; }",
    "function returned(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = makeAdder(value); return (f(2), f(3)); }",
    "function shared(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " let g: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; }; return (f(2), g(3)); }",
    "function selfCell(value: Word) returns (Word) {",
    " let loop: function(Word) returns (Word);",
    " loop = lam(n: Word) -> Word { return n == 0 ? value : loop(n - 1); }; return loop(3); }",
    "function failure() returns (Word) { let f: function(Word) returns (Word); return f(0); }"
  ] }]
}

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def compileNamed (program : CheckedProgram) (name : String) (preference : BackendPreference) : IO CompiledEntry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"{name}: function fixture missing")
  match compileChecked program (.declaration signature.id [])
      { backendPreference := preference, specializationBudget := 100, stagingFuel := 200 } with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError s!"{name}: compilation failed: {reprStr error}")

private def execution : RunOptions := { inputValidationFuel := 100, executionFuel := 30000 }

private def testValues (program : CheckedProgram) : IO Unit := do
  let pair := Core.Value.pair (scalar 4) (scalar 7)
  for preference in [BackendPreference.automatic, .core] do
    for (name, expected) in [("named", scalar 3), ("returned", pair), ("shared", pair), ("selfCell", scalar 2)] do
      let compiled ← compileNamed program name preference
      assertTrue (compiled.backend == .core) s!"{name}: function program did not select Core"
      for _ in [0, 1] do
        match compiled.runCore [scalar 2] execution with
        | .ok (.coreLanguageResult (.succeeded value _)) =>
            assertTrue (value == expected) s!"{name}: capture, indirect call or entry reuse changed the value"
        | result => throw (IO.userError s!"{name}: Core function run failed: {reprStr result}")
  for name in ["returned", "shared"] do
    let compiled ← compileNamed program name .typedSource
    match compiled.runTyped [.word (word 2)] execution with
    | .ok (.typedSource (.done (.product (.word left) (.word right)) _)) =>
        assertTrue (left == word 4 && right == word 7) s!"{name}: Core and source capture results differ"
    | result => throw (IO.userError s!"{name}: source comparison failed: {reprStr result}")

private def testFailure (program : CheckedProgram) : IO Unit := do
  let compiled ← compileNamed program "failure" .core
  let function ← match program.functions.find? (·.declaration == compiled.key.declaration) with
    | some function => pure function
    | none => throw (IO.userError "failure: source function missing")
  let reads := function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
        | .reference "f" (.local binder) => some (node, binder)
        | _ => none
    | _ => none
  let (node, binder) ← match reads with
    | [read] => pure read
    | _ => throw (IO.userError "failure: function read occurrence missing")
  match compiled.runCore [] execution with
  | .ok (.coreLanguageResult (.failed reason _)) =>
      assertTrue (decide (compiled.coreFailureDiagnostic? reason = some {
        error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span }))
        "failed indirect callee lost its source occurrence"
  | result => throw (IO.userError s!"failure: indirect callee did not fail: {reprStr result}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"function fixture failed checking: {reprStr errors}")
  testValues program
  testFailure program

end Tests.SourceCompilerFunctions
