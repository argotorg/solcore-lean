import Solcore.Frontend.SourceCompilerSession
import Solcore.Frontend.SourceCompiler

/-! Actual checked local polymorphic lambdas run through Core. Every concrete
instance captures the original lexical cells, and nested choices retain their
full cumulative contexts. -/
set_option autoImplicit false
namespace Tests.SourceCoreLocalPolymorphicExecution
open Solcore Solcore.Frontend SourceCompiler
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function identity<T>(value: T) returns (T) { return value; }",
    "function local(flag: Bool) returns (Word, Bool) { let f = lam(item) { return identity(item); }; return (f(11), f(flag)); }",
    "function nested(flag: Bool) returns (Word, Bool) { let outer = lam(item) { let inner = lam(value) { return identity(value); }; return inner(item); }; return (outer(13), outer(flag)); }",
    "function recursiveContext(flag: Bool) returns (Word, Bool) { let outer = lam(value) { let middle = lam(item) { let inner = lam(innerValue) { return identity(innerValue); }; return inner(item); }; return middle(value); }; return (outer(15), outer(flag)); }",
    "function sameInnerType(flag: Bool) returns (Word, Word) { let outer = lam(value) { let inner = lam(item) { return item; }; return inner(1); }; return (outer(1), outer(flag)); }",
    "function dependentInner(flag: Bool) returns ((Word, Word), (Bool, Bool)) { let outer = lam(value) { let inner = lam(item) { return (value, item); }; return inner(value); }; return (outer(1), outer(flag)); }",
    "function sharedCapture(flag: Bool) returns (Word) { let total: Word = 0; let f = lam(item) { total += 1; return item; }; f(1); f(flag); f(2); return total; }",
    "function unused() returns (Word) { let outer = lam(value) { let inner = lam(item) { return item; }; return inner(value); }; return 9; }",
    "enum Box<T> { Full(T) }",
    "function intermediate(flag: Bool) returns (Word, Bool) { let f = lam(item) { let box = Box.Full(item); match (box) { case .Full(value) { return value; } } }; return (f(17), f(flag)); }"
  ]}]
}
private def compile (program : CheckedProgram) (name : String) (backend : BackendPreference) : IO CompiledEntry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"local runtime fixture missing: {name}")
  let options : CompileOptions := {backendPreference := backend, stagingFuel := 128, specializationBudget := 32}
  match compileChecked program (.declaration signature.id) options with
  | .ok result => pure result
  | .error error =>
      let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
        | .ok (.complete plan) => pure plan
        | result => throw (IO.userError s!"local runtime plan failed: {reprStr result}")
      throw (IO.userError s!"local runtime compilation failed: {name}: {reprStr error}; general: {reprStr (SourceCoreSession.Recipe.prepareAutomatic program plan 128)}")
private def check (program : CheckedProgram) (name : String) (arguments : List Core.Value) (expected : Core.Value) : IO Unit := do
  for backend in [BackendPreference.core, .automatic] do
    let compiled ← compile program name backend
    unless compiled.backend == .core do throw (IO.userError s!"{name} selected legacy runtime")
    for _ in [0, 1] do
      match compiled.runCore arguments {executionFuel := 65536} with
      | .ok (.coreLanguageResult (.succeeded value _)) =>
          unless value == expected do throw (IO.userError s!"{name} wrong result: {reprStr value}")
      | result => throw (IO.userError s!"{name} Core run failed: {reprStr result}")
    match compiled.runCore arguments {executionFuel := 0} with
    | .ok (.coreLanguageResult (.outOfFuel state)) =>
        match Core.LanguageResult.observeResult (Core.runStateful 65536 state) with
        | .succeeded value _ => unless value == expected do throw (IO.userError s!"{name} resume changed result")
        | result => throw (IO.userError s!"{name} resume failed: {reprStr result}")
    | result => throw (IO.userError s!"{name} did not suspend: {reprStr result}")
def run : IO Unit := do
  let program ← match checkProgram workspace 4096 with
    | .ok result => pure result
    | .error error => throw (IO.userError s!"local runtime source rejected: {reprStr error}")
  for flag in [true, false] do
    check program "local" [.bool flag] (.pair (.word (w 11)) (.bool flag))
    check program "nested" [.bool flag] (.pair (.word (w 13)) (.bool flag))
    check program "recursiveContext" [.bool flag] (.pair (.word (w 15)) (.bool flag))
    check program "sameInnerType" [.bool flag] (.pair (.word (w 1)) (.word (w 1)))
    check program "dependentInner" [.bool flag] (.pair (.pair (.word (w 1)) (.word (w 1))) (.pair (.bool flag) (.bool flag)))
    check program "sharedCapture" [.bool flag] (.word (w 3))
    check program "intermediate" [.bool flag] (.pair (.word (w 17)) (.bool flag))
  check program "unused" [] (.word (w 9))
end Tests.SourceCoreLocalPolymorphicExecution
