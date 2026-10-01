import Solcore.Test.SourceCompilerFeatureSupport

set_option autoImplicit false
namespace Tests.SourceCompilerFunctions
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

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

private def testValues (program : CheckedProgram) : IO Unit := do
  let pair : Value := .product (scalar 4) (scalar 7)
  for (name, expected) in [("named", scalar 3), ("returned", pair), ("shared", pair), ("selfCell", scalar 2)] do
    let compiled ← compileNamed program name
    for _ in [0, 1] do
      require ((← compiled.run [scalar 2]) == expected)
        s!"{name}: capture, indirect call or cached entry reuse changed"
    compiled.checkResume [scalar 2] expected

private def testFailure (program : CheckedProgram) : IO Unit := do
  let compiled ← compileNamed program "failure"
  let function ← match program.functions.find? (·.declaration == compiled.key.declaration) with
    | some function => pure function | none => throw (IO.userError "failure source function missing")
  let reads := function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
      | .reference "f" (.local binder) => some (node, binder) | _ => none
    | _ => none
  let (node, binder) ← match reads with
    | [read] => pure read | _ => throw (IO.userError "failure occurrence missing")
  let invocation ← compiled.invoke []
  match invocation.outcome with
  | .failed reason _ =>
      require (decide ((← invocation.diagnostic reason) = some {
        error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span }))
        "failed indirect callee lost its source occurrence"
  | _ => throw (IO.userError "uninitialized indirect callee did not fail")

def run : IO Unit := do
  let program ← get "function checking" (checkProgram workspace)
  testValues program
  testFailure program
end Tests.SourceCompilerFunctions
