import Solcore.Frontend.SourceCompiler

/-!
# Match binder stages

A binder of one of several written scrutinees, `match (x, flag)`, takes that scrutinee's stage, as
upstream's match bindings inherit only their own scrutinee's availability
(`match_bindings_inherit_only_their_own_scrutinee_availability`). The parts reach Lean's staging as
`MatchResolution.parts`, and a tuple pattern's components take their stages
(`Staging.MatchCaseStages.parts`). A binder of a comptime parameter's part reaches a comptime
parameter while the other part is runtime: in either position, nested in a comptime pair, the
middle of three, beside a runtime binder, through a local and beside a default arm
(`testAccepted`). A binder of a runtime part is refused there, as upstream refuses it (`SC0240`),
and so is a binder of one tuple-valued scrutinee, `match ((x, flag))`, which is one value
(`testRefused`). One comptime scrutinee keeps its stage (`testUnchanged`). Each case is a source
upstream's checker was probed with at both pins, and an accepted one runs at 9 and 2^256 − 1 with
the result upstream's checked Hull gives. A part assigned later is refused, where upstream accepts
it (`testDifferences`).
-/

set_option autoImplicit false

namespace Tests.MatchBinderStages

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def maximum : Nat := 2 ^ 256 - 1

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

private def take : String := "function take(comptime value: word) returns (word) { return value; }"

/-- A two-scrutinee match's tuple pattern splits into one component per scrutinee, a nested
pattern whole; a pattern of another arity, or of one scrutinee, does not split. -/
example : SourceSemantics.Staging.splitPatternComponents 2
    [.tuple 2, .wildcard, .wildcard, .wildcard] =
      some [[.tuple 2, .wildcard, .wildcard], [.wildcard]] := by decide
example : SourceSemantics.Staging.patternComponents (.tuple [.wildcard, .wildcard]) 3 = none := by
  decide
example : SourceSemantics.Staging.patternComponents (.tuple [.wildcard, .wildcard]) 0 = none := by
  decide

/-- The binders upstream takes from a comptime part, with its results. -/
private def testAccepted : IO Unit := do
  -- C316, the form of upstream's fixture 001 at `word`.
  expectResults "the comptime part's binder" [take,
      "function get(comptime x: word, flag: bool) returns (word) {",
      "  match (x, flag) { case (y, true) { return take(y); } case (y, false) { return 0; } }",
      "}"] "get(3, true)" [3, 3]
  -- Fixture 001's arm: the runtime part's binder shadows the comptime parameter.
  expectResults "beside a binder that shadows the parameter" [take,
      "function choose(comptime x: word, flag: bool) returns (word) {",
      "  match (x, flag) { case (y, x) { return take(y); } }",
      "}"] "choose(3, true)" [3, 3]
  expectResults "nested in a comptime pair" [take,
      "function choose(comptime x: (word, word), flag: bool) returns (word) {",
      "  match (x, flag) { case ((y, z), x) { return take(z); } }",
      "}"] "choose((3, 4), true)" [4, 4]
  expectResults "the comptime part second" [take,
      "function get(comptime x: word, w: word) returns (word) {",
      "  match (w, x) { case (y2, y) { return take(y); } }",
      "}"] "get(3, 5)" [3, 3]
  expectResults "the middle of three" [take,
      "function get(a: word, comptime x: word, flag: bool) returns (word) {",
      "  match (a, x, flag) { case (p, y, f) { return take(y); } }",
      "}"] "get(1, 3, true)" [3, 3]
  expectResults "beside a runtime binder used at runtime" [take,
      "function get(comptime x: word, flag: bool) returns (word) {",
      "  match (x, flag) { case (y, f) { if (f) { return take(y); } return 0; } }",
      "}"] "get(3, true)" [3, 3]
  expectResults "through a local of the comptime part" [take,
      "function get(comptime x: word, flag: bool) returns (word) {",
      "  let v: word = x;",
      "  match (v, flag) { case (y, f) { return take(y); } }",
      "}"] "get(3, true)" [3, 3]
  expectResults "beside a default arm" [take,
      "function get(comptime x: word, flag: bool) returns (word) {",
      "  match (x, flag) { case (y, true) { return take(y); } default { return 0; } }",
      "}"] "get(3, true)" [3, 3]

/-- The binders upstream refuses at a comptime parameter (`SC0240`). -/
private def testRefused : IO Unit := do
  -- C313: one tuple-valued scrutinee is one value, runtime while `flag` is.
  expectRefused "one tuple-valued scrutinee" [take,
      "function get(comptime x: word, flag: bool) returns (word) {",
      "  match ((x, flag)) { case (y, true) { return take(y); } case (y, false) { return 0; } }",
      "}"] "get(3, true)" "compile"
  -- Fixture 002's form at `word`.
  expectRefused "the runtime part's binder" [take,
      "function get(comptime x: word, w: word) returns (word) {",
      "  match (x, w) { case (y, y2) { return take(y2); } }",
      "}"] "get(3, 5)" "compile"
  -- Fixture 003's order.
  expectRefused "the runtime part's binder, first" [take,
      "function get(comptime x: word, w: word) returns (word) {",
      "  match (w, x) { case (y2, y) { return take(y2); } }",
      "}"] "get(3, 5)" "compile"

/-- One scrutinee, as Lean read it before (C314). -/
private def testUnchanged : IO Unit := do
  expectResults "one comptime scrutinee" [take,
      "function get(comptime x: word) returns (word) { match (x) { case y { return take(y); } } }"]
    "get(3)" [3, 3]

/-- The difference from upstream that stays. -/
private def testDifferences : IO Unit := do
  -- Upstream follows the assigned value and accepts it with 4; Lean's staging defers a binder
  -- assigned anywhere in its declaration, so the part, and its binder, are deferred.
  expectRefused "a part assigned later" [take,
      "function get(comptime x: word, flag: bool) returns (word) {",
      "  let v: word = x;",
      "  v = 4;",
      "  match (v, flag) { case (y, f) { return take(y); } }",
      "}"] "get(3, true)" "compile"

def run : IO Unit := do
  testAccepted
  testRefused
  testUnchanged
  testDifferences
  IO.println "match binder stages: upstream's forms, refusals and results, and the difference GREEN"

end Tests.MatchBinderStages
