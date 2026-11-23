import Solcore.Frontend.SourceCompiler

/-!
# Comptime locals

A `let` annotated `comptime<T>` at its top, as upstream writes a local that holds a value known
while staged: Lean reads it at `T` and requires its binder to be comptime-staged in Lean's own stage
analysis (`Syntax.Unchecked.mark`, `SourceCompilationPlan.comptimeLetStageMismatch`). It takes a
constant function's value, a literal, another comptime local, an operator on literals and a value
passed through a comptime parameter, at `word` and `bool`, also inside a constant function, and it
reaches runtime arithmetic and a comptime parameter (`testAccepted`). The forms around it keep
their answers (`testUnchanged`). A runtime initializer, a later assignment and a missing initializer
are refused, as upstream refuses them (`SC0241`, `SC0411`, `SC0409`) (`testRefused`). Each case
is a source upstream's pinned checker was probed with, and an accepted one runs at 9 and 2^256 − 1
with the results upstream's checked Hull gives. Two differences stay (`testDifferences`): an
ordinary function's call on literals, which upstream evaluates while staged and Lean's staging
defers, is refused; a comptime local in a tuple, which upstream's Hull lowering cannot represent
(`SC0411`), is accepted.
-/

set_option autoImplicit false

namespace Tests.ComptimeLocals

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def maximum : Nat := 2 ^ 256 - 1

private def same : List Nat := [9, maximum]

/-- A body that starts with `{` is `main`'s statements, any other the expression it returns. -/
private def workspace (declarations : List String) (body : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    { path := "main.solc", content := String.intercalate "\n" (["pragma solcore;"] ++
        declarations ++ [s!"function main(a0: word) returns (word) " ++
          (if body.startsWith "{" then body else s!"\{ return {body}; }")]) }]
  externalLibraries := []
}

/-- The function `main` loaded, checked, compiled and run at each input, or the stage that
refused it. -/
private def runMain (raw : Workspace.RawWorkspace) (inputs : List Nat) :
    IO (Except String (List Nat)) := do
  let loaded ← match loadProgram raw with
    | .ok loaded => pure loaded
    | .error _ => return .error "load"
  let checked ← match checkLoadedProgram loaded 4096 with
    | .ok checked => pure checked
    | .error _ => return .error "check"
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
    (expected : List Nat) : IO Unit := do
  let found ← runMain (workspace declarations body) [9, maximum]
  assertTrue (match found with | .ok results => results == expected | .error _ => false)
    s!"{label}: expected {expected}, got {reprStr found}"

private def expectRefused (label : String) (declarations : List String) (body : String)
    (stage : String) : IO Unit := do
  let found ← runMain (workspace declarations body) [9]
  assertTrue (match found with | .error refused => refused == stage | .ok _ => false)
    s!"{label}: expected a refusal at {stage}, got {reprStr found}"

/-- A comptime parameter's value, given as a comptime result. -/
private def static : String := "function s(comptime v: word) returns (comptime<word>) { return v; }"

private def constant : String := "function k() returns (comptime<word>) { return 7; }"

private def throughStatic : String := "function k() returns (comptime<word>) { return s(7); }"

private def withLocal : String :=
  "function k() returns (comptime<word>) { let v: word = 0; if (true) { v = 5; } return s(v); }"

/-- The comptime locals upstream accepts, with its results. -/
private def testAccepted : IO Unit := do
  expectResults "a constant function's value" [constant]
    "{ let c: comptime<word> = k(); return c; }" [7, 7]
  expectResults "added to a runtime word" [constant]
    "{ let c: comptime<word> = k(); return a0 + c; }" [16, 6]
  expectResults "through a comptime parameter" [static, throughStatic]
    "{ let c: comptime<word> = k(); return c; }" [7, 7]
  expectResults "a constant function with a local" [static, withLocal]
    "{ let c: comptime<word> = k(); return c; }" [5, 5]
  expectResults "the comptime emitter's method, small" [static, withLocal]
    "{ let v: comptime<word> = k(); let r: word = (a0 + v) + v; return r; }" [19, 9]
  expectResults "a literal" [] "{ let c: comptime<word> = 7; return c; }" [7, 7]
  expectResults "to a comptime parameter" [static, throughStatic]
    "{ let c: comptime<word> = k(); return s(c); }" [7, 7]
  expectResults "from a comptime local" [constant]
    "{ let c: comptime<word> = k(); let d: comptime<word> = c; return d; }" [7, 7]
  expectResults "from a comptime parameter's call" [static]
    "{ let c: comptime<word> = s(7); return c; }" [7, 7]
  expectResults "from an operator on literals" [] "{ let c: comptime<word> = 3 + 4; return c; }"
    [7, 7]
  expectResults "at bool" [] "{ let c: comptime<bool> = true; if (c) { return 1; } return 2; }" [1, 1]
  expectResults "in a constant function" [static,
      "function k() returns (comptime<word>) { let v: comptime<word> = 5; return s(v); }"]
    "k()" [5, 5]
  expectResults "from a word local of a comptime call" [constant]
    "{ let w: word = k(); let c: comptime<word> = w; return c; }" [7, 7]
  expectResults "in a runtime branch" [constant]
    "{ let c: comptime<word> = k(); if (a0 == 9) { return c; } return 0; }" [7, 0]

/-- The forms around a comptime local, as Lean read them before. -/
private def testUnchanged : IO Unit := do
  expectResults "a constant function's value, returned" [constant] "k()" [7, 7]
  expectResults "a constant function's value at a word local" [constant]
    "{ let c: word = k(); return c; }" [7, 7]
  expectResults "a literal to a comptime parameter" [static] "s(7)" [7, 7]
  expectResults "a word local of a comptime call to a comptime parameter" [static, throughStatic]
    "{ let c: word = k(); return s(c); }" [7, 7]

/-- The forms upstream refuses. -/
private def testRefused : IO Unit := do
  expectRefused "a runtime initializer" [] "{ let c: comptime<word> = a0; return c; }" "compile"
  expectRefused "a later runtime assignment" [constant]
    "{ let c: comptime<word> = k(); c = a0; return c; }" "compile"
  expectRefused "no initializer" [] "{ let c: comptime<word>; return 0; }" "compile"
  expectRefused "a runtime argument to a comptime parameter" [static] "s(a0)" "compile"
  expectRefused "comptime<T> as a parameter type"
    ["function f(x: comptime<word>) returns (word) { return x; }"] "f(7)" "load"

/-- The two differences from upstream that stay. -/
private def testDifferences : IO Unit := do
  -- Upstream evaluates `r(7)` while staged and accepts it with 7; Lean's staging defers an
  -- ordinary function's call, so the local is not comptime-staged.
  expectRefused "an ordinary function's call on literals"
    ["function r(x: word) returns (word) { return x; }"]
    "{ let c: comptime<word> = r(7); return c; }" "compile"
  -- Upstream's Hull lowering cannot represent `pair(comptime word, word)` (`SC0411`); Lean's
  -- local holds a `word`.
  expectResults "in a tuple" [constant]
    ("{ let c: comptime<word> = k(); let p: (word, word) = (c, a0); " ++
      "match (p) { case (x, y) { return x; } } }") [7, 7]

def run : IO Unit := do
  testAccepted
  testUnchanged
  testRefused
  testDifferences
  IO.println "comptime locals: upstream's forms, refusals and results, and the two differences GREEN"

end Tests.ComptimeLocals
