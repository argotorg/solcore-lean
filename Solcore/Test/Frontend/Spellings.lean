import Solcore.Frontend.SourceCompiler

/-!
# The builtin types' spellings

Upstream's builtin types are `word`, `bool` and `()`, looked up after a module's own types and
its imports' (`lookup_type`). `Word`, `Bool`, `Unit` and `unit` name nothing builtin, as
upstream's `SC0103` refuses them. So a capitalized spelling as a parameter, a result, a `let`, a
type argument or in a function type is an unknown type name (C101, C103, C105, C106, C108 to
C110), the lowercase ones run (C102, C104, C107), and a program's own or an imported `Word` or
`Bool` is its own (C111 to C113). Each case is a probe of upstream's pinned checker; an accepted
one runs at 9 and 2^256 − 1 and gives upstream's results.
-/

set_option autoImplicit false

namespace Tests.Spellings

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def maximum : Nat := 2 ^ 256 - 1

/-- `main.solc` with the declarations and `main`'s body, beside library modules. -/
private def workspace (declarations : List String) (body : String)
    (libraries : List (String × List String)) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources :=
    { path := "main.solc", content := String.intercalate "\n" (["pragma solcore;"] ++
        declarations ++ [s!"function main(a0: word) returns (word) \{ {body} }"]) } ::
      libraries.map fun (path, lines) =>
        { path, content := String.intercalate "\n" ("pragma solcore;" :: lines) }
  externalLibraries := []
}

/-- What refused a program: an unknown type name in a signature or a body, or another stage. -/
private def refusal : ProgramCheckError → String
  | .signature (.typeResolution _ (.unknownTypeName components)) =>
      s!"unknown type {".".intercalate components}"
  | .inference { error := .typeResolution (.unknownTypeName components), .. } =>
      s!"unknown type {".".intercalate components}"
  | .signature _ => "signatures"
  | .inference _ => "inference"
  | .loading _ => "load"
  | _ => "check"

/-- The function `main` loaded, checked, compiled and run at each input, or what refused it. -/
private def runMain (raw : Workspace.RawWorkspace) (inputs : List Nat) :
    IO (Except String (List Nat)) := do
  let loaded ← match loadProgram raw with
    | .ok loaded => pure loaded
    | .error _ => return .error "load"
  let checked ← match checkLoadedProgram loaded 4096 with
    | .ok checked => pure checked
    | .error errors => return .error ((errors.map refusal).eraseDups.toString)
  let seed := SourceCompiler.Seed.named loaded.workspace.entry.toModuleId "main"
  let options : SourceCompiler.Options :=
    {checkingFuel := 4096, compilationFuel := 4096, specializationBudget := 1024}
  let compiled ← match SourceCompiler.compileChecked checked [seed] options with
    | .ok compiled => pure compiled
    | .error _ => return .error "compile"
  let key ← match compiled.keys with
    | [key] => pure key
    | _ => return .error "keys"
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let session ← match bootstrap.resume 1000000 with
    | .ready session => pure session
    | _ => return .error "boot"
  let mut results := []
  for input in inputs do
    match ← session.run key [.word (Core.Word.ofNatModulo input)]
        {inputValidationFuel := 4096, outputValidationFuel := 4096, executionFuel := 1000000} with
    | .ok (.succeeded completion) => match completion.value with
      | .word word => results := results ++ [word.val]
      | _ => return .error "value"
    | _ => return .error "run"
  return .ok results

private def expectResults (label : String) (declarations : List String) (body : String)
    (expected : List Nat) (libraries : List (String × List String) := []) : IO Unit := do
  let found ← runMain (workspace declarations body libraries) [9, maximum]
  assertTrue (match found with | .ok results => results == expected | .error _ => false)
    s!"{label}: expected {expected}, got {reprStr found}"

private def expectRefused (label : String) (declarations : List String) (body : String)
    (reasons : List String) (libraries : List (String × List String) := []) : IO Unit := do
  let found ← runMain (workspace declarations body libraries) [9]
  assertTrue (match found with | .error refused => refused == reasons.toString | .ok _ => false)
    s!"{label}: expected a refusal {reasons}, got {reprStr found}"

/-- C101 to C110: each spelling as a parameter, a result, a `let`, a type argument and in a
function type, the capitalized ones refused and the lowercase ones run. -/
private def testSpellings : IO Unit := do
  expectRefused "C101 Word as a parameter and result type"
    ["function g(x: Word) returns (Word) { return x; }"] "return g(a0);" ["unknown type Word"]
  expectResults "C102 word, the same"
    ["function g(x: word) returns (word) { return x; }"] "return g(a0);" [9, maximum]
  expectRefused "C103 Bool as a parameter type"
    ["function f(b: Bool) returns (word) { if (b) { return 1; } return 0; }"] "return f(true);"
    ["unknown type Bool"]
  expectResults "C104 bool, the same"
    ["function f(b: bool) returns (word) { if (b) { return 1; } return 0; }"] "return f(true);"
    [1, 1]
  expectRefused "C105 Unit as a result type"
    ["function u(x: word) returns (Unit) { return (); }"] "u(a0); return a0;" ["unknown type Unit"]
  expectRefused "C106 unit as a result type"
    ["function u(x: word) returns (unit) { return (); }"] "u(a0); return a0;" ["unknown type unit"]
  expectResults "C107 () as a result type"
    ["function u(x: word) returns (()) { return (); }"] "u(a0); return a0;" [9, maximum]
  expectRefused "C108 Word at a let" [] "let x: Word = a0; return x;" ["unknown type Word"]
  expectRefused "C109 Word in a type argument"
    ["enum Box<a> { B(a) }",
      "function un(b: Box<Word>) returns (word) { match (b) { case Box.B(x) { return x; } } }"]
    "return un(Box.B(a0));" ["unknown type Word"]
  expectRefused "C110 Bool in a function type"
    ["function apply(g: function (word) returns (Bool), x: word) returns (word) { if (g(x)) { return 1; } return 0; }",
      "function yes(x: word) returns (bool) { return true; }"]
    "return apply(yes, a0);" ["unknown type Bool"]

/-- C111 to C113: a program's own or an imported type named `Word` or `Bool` is its own, as
upstream looks a builtin's name up after the module's own types and its imports'. -/
private def testOwnNames : IO Unit := do
  expectResults "C111 a program's own type named Word"
    ["enum Word { W }", "function g(x: Word) returns (word) { return 5; }"] "return g(Word.W);"
    [5, 5]
  expectResults "C112 a program's own type named Bool"
    ["enum Bool { T, F }", "function g(x: Bool) returns (word) { return 5; }"] "return g(Bool.T);"
    [5, 5]
  expectResults "C113 an imported type named Word"
    ["import { Word } from wordlib;", "function g(x: Word) returns (word) { return 5; }"]
    "return g(Word.W);" [5, 5] [("wordlib.solc", ["export { Word(*) };", "enum Word { W }"])]

def run : IO Unit := do
  testSpellings
  testOwnNames
  IO.println "the builtin types' spellings: upstream's verdicts and results GREEN"

end Tests.Spellings
