import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual checked local polymorphic lambdas run through Core. Every concrete
instance captures the original lexical cells, and nested choices retain their
full cumulative contexts. -/
set_option autoImplicit false
namespace Tests.SourceCoreLocalPolymorphicExecution
open Solcore Solcore.Frontend SourceCoreExecution
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function qualified(flag: Bool) returns (Word, Bool) { let f = lam(item) { return keep(item); }; return (f(19), f(flag)); }",
    "function qualifiedNested(flag: Bool) returns (Word, Word) { let outer = lam(value) { keep(value); let inner = lam(item) { return keep(item); }; return inner(1); }; return (outer(1), outer(flag)); }",
    "function qualifiedCapture(flag: Bool) returns (Word) { let count: Word = 0; let f = lam(item) { count += 1; return keep(item); }; f(1); f(flag); return count; }",
    "type WordFunction = function(Word) returns (Word);",
    "function qualifiedMaker(seed: Word) returns (WordFunction) { let count: Word = seed; let f = lam(item) { keep(item); count += 1; return count; }; return f; }",
    "function useFunction(f: WordFunction, value: Word) returns (Word) { return f(value); }",
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
private def check (program : CheckedProgram) (name : String) (arguments : List Value) (expected : Value) : IO Unit := do
  let compiled ← SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 32, compilationFuel := 1000}
  for _ in [0, 1] do
    unless (← compiled.run arguments) == expected do
      throw (IO.userError s!"{name} changed the specialized result")
  compiled.checkResume arguments expected 0

def run : IO Unit := do
  let program ← match checkProgram workspace 4096 with
    | .ok result => pure result
    | .error error => throw (IO.userError s!"local runtime source rejected: {reprStr error}")
  for flag in [true, false] do
    check program "qualified" [.bool flag] (.product (.word (w 19)) (.bool flag))
    check program "qualifiedNested" [.bool flag] (.product (.word (w 1)) (.word (w 1)))
    check program "qualifiedCapture" [.bool flag] (.word (w 2))
    check program "local" [.bool flag] (.product (.word (w 11)) (.bool flag))
    check program "nested" [.bool flag] (.product (.word (w 13)) (.bool flag))
    check program "recursiveContext" [.bool flag] (.product (.word (w 15)) (.bool flag))
    check program "sameInnerType" [.bool flag] (.product (.word (w 1)) (.word (w 1)))
    check program "dependentInner" [.bool flag] (.product (.product (.word (w 1)) (.word (w 1))) (.product (.bool flag) (.bool flag)))
    check program "sharedCapture" [.bool flag] (.word (w 3))
    check program "intermediate" [.bool flag] (.product (.word (w 17)) (.bool flag))
  check program "unused" [] (.word (w 9))
  let seeds ← ["qualifiedMaker", "useFunction"].mapM fun name => do
    match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
    | _ => throw (IO.userError s!"qualified function root missing: {name}")
  let shared ← match SourceCoreExecution.compileChecked program seeds {compilationFuel := 128, specializationBudget := 32} with
    | .ok shared => pure shared
    | .error error => throw (IO.userError s!"qualified function session failed: {reprStr error}")
  let artifact ← shared.open
  let session ← SourceCompilerFeatureSupport.boot artifact
  let producer ← match shared.keys[0]? with | some key => pure key | none => throw (IO.userError "qualified producer missing")
  let consumer ← match shared.keys[1]? with | some key => pure key | none => throw (IO.userError "qualified consumer missing")
  match ← session.run producer [.word (w 10)] {executionFuel := 300000} with
  | .ok (.succeeded made) =>
      match ← made.session.run consumer [made.value, .word (w 1)] {executionFuel := 300000} with
      | .ok (.succeeded first) =>
          unless first.value == .word (w 11) do throw (IO.userError "qualified closure lost its capture or globals")
          match ← first.session.run consumer [made.value, .word (w 2)] {executionFuel := 300000} with
          | .ok (.succeeded second) =>
              unless second.value == .word (w 12) do throw (IO.userError "qualified closure lost mutation across calls")
          | _ => throw (IO.userError "qualified closure second invocation failed")
      | _ => throw (IO.userError "qualified closure invocation failed")
  | _ => throw (IO.userError "qualified closure export failed")
  IO.println "actual Core local polymorphism and qualified shared captures GREEN"
end Tests.SourceCoreLocalPolymorphicExecution
