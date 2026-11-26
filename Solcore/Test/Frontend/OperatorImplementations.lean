import Solcore.Frontend.SourceCompiler

/-!
# Operators beside a program's implementation of their trait

The user's rule of 2026-11-23 ("使用箇所に絞る"): an operator that Lean takes as its builtin at
`word` or a fixed-width type is refused where a program's implementation of its trait there gives
it a second meaning (`builtinOperatorMeetsImplementation`), whether the use runs or not. The trait
must declare the operator's method and be one that upstream's lookup reaches under the
operator's trait name: in the module's scope, or through its imports, plain ones included, under
the name a scope sees it by, an alias among them (`testRefusedUses`). An implementation of
`Shl` or `Shr` at one of those types is refused where it is declared, as Lean's shifts never take
it (`testRefusedShifts`). Generic code, which runs the implementation as upstream does, a trait of
the operator's name without its method, a program's own type and `bool`, where Lean has no
builtin, refuse nothing (`testAccepted`). An operator's trait is the one declared with its name,
whatever a scope calls it: the declared `Add` imported as `Plus` runs `+` in generic code, and a
`Plus` imported as `Add` is no `Add`, refused at inference where upstream runs it by name
(`testDeclaredName`). Each case is a probe of upstream's pinned checker
(`optrule_probe.py`); an accepted one runs at 9 and 2^256 − 1 and gives upstream's results, but
for the traits without the method, which upstream refuses (`SC0207`).
-/

set_option autoImplicit false

namespace Tests.OperatorImplementations

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

/-- What refused a program: the rule at a use, in a function or a method, the rule at a shift
implementation, or another stage. -/
private def refusal : ProgramCheckError → String
  | .inference { error := .builtinOperatorMeetsImplementation trait _ _, .. } => s!"meets {trait}"
  | .inference _ => "inference"
  | .methodInference _ (.builtinOperatorMeetsImplementation trait _ _) => s!"method meets {trait}"
  | .methodInference _ _ => "method inference"
  | .signature (.shiftImplementationAtBuiltinType _) => "shift"
  | .signature _ => "signatures"
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

private def addTrait : String := "trait Add<a> { function add(x: a, y: a) returns (a); }"
private def addFirst : String :=
  "impl Add<word> { function add(x: word, y: word) returns (word) { return x; } }"
private def eqTrait : String := "trait Eq<a> { function eq(x: a, y: a) returns (bool); }"
private def bitNotTrait : String := "trait BitNot<a> { function bnot(x: a) returns (a); }"
private def shlTrait : String := "trait Shl<a, b> { function bshl(x: a, y: b) returns (a); }"
private def box : List String := [
  "enum Box { Box(word) }",
  "function unbox(b: Box) returns (word) { match (b) { case .Box(v) { return v; } } }"]
private def condition (test : String) : String := s!"if ({test}) \{ return 1; } return 0;"

/-- Uses where the builtin and a program's implementation meet, each refused where it is. -/
private def testRefusedUses : IO Unit := do
  expectRefused "+ at word" [addTrait, addFirst] "return a0 + a0;" ["meets Add"]
  expectRefused "== at word" [eqTrait,
    "impl Eq<word> { function eq(x: word, y: word) returns (bool) { return true; } }"]
    (condition "a0 == 9") ["meets Eq"]
  expectRefused "> at word" [eqTrait, "trait Ord<a> where a: Eq { function gt(x: a, y: a) returns (bool); }",
    "impl Eq<word> { function eq(x: word, y: word) returns (bool) { return true; } }",
    "impl Ord<word> { function gt(x: word, y: word) returns (bool) { return true; } }"]
    (condition "a0 > 9") ["meets Ord"]
  expectRefused "~ at word" [bitNotTrait,
    "impl BitNot<word> { function bnot(x: word) returns (word) { return 5; } }"]
    "return ~a0;" ["meets BitNot"]
  expectRefused "an in-place ~ at word" [bitNotTrait,
    "impl BitNot<word> { function bnot(x: word) returns (word) { return 5; } }"]
    "let x: word = a0; x ~=; return x; " ["meets BitNot"]
  expectRefused "+= at word" [addTrait, addFirst] "let x: word = a0; x += 1; return x;"
    ["meets Add"]
  expectRefused "a + in a function that generic code calls" [addTrait, addFirst,
    "function inc(x: word) returns (word) { return x + 1; }",
    "function applyAdd<t>(x: t, f: function (t) returns (t)) returns (t) where t: Add { return f(x) + x; }"]
    "return applyAdd(a0, inc);" ["meets Add"]
  expectRefused "+ inside the implementation's own add" [addTrait,
    "impl Add<word> { function add(x: word, y: word) returns (word) { return x + y; } }"]
    "return a0;" ["method meets Add"]
  expectRefused "Add at word through primAddWord, upstream's own form" [addTrait,
    "impl Add<word> { function add(x: word, y: word) returns (word) { return primAddWord(x, y); } }"]
    "return a0 + 1;" ["meets Add"]
  expectRefused "a + in a function nothing calls" [addTrait, addFirst,
    "function unused(x: word) returns (word) { return x + 1; }"] "return a0;" ["meets Add"]
  expectRefused "a generic implementation" [addTrait,
    "impl<a> Add<a> { function add(x: a, y: a) returns (a) { return y; } }"]
    "return a0 + 1;" ["meets Add"]
  expectRefused "an Add of two parameters" [
    "trait Add<a, b> { function add(x: a, y: b) returns (a); }",
    "impl Add<word, word> { function add(x: word, y: word) returns (word) { return 7; } }"]
    "return 1 + 2;" ["meets Add"]
  expectRefused "+ at uint8" [addTrait,
    "impl Add<uint8> { function add(x: uint8, y: uint8) returns (uint8) { return x; } }"]
    "return Typedef.rep(uint8(3) + uint8(4));" ["meets Add"]
  expectRefused "unchecked + at uint8" [
    "trait UncheckedAdd<a> { function add(x: a, y: a) returns (a); }",
    "impl UncheckedAdd<uint8> { function add(x: uint8, y: uint8) returns (uint8) { return x; } }"]
    "unchecked { return Typedef.rep(uint8(3) + uint8(4)); }" ["meets UncheckedAdd"]
  let lib := [("lib.solc", ["export { Add };", addTrait, addFirst])]
  expectRefused "the trait and implementation selected from lib" ["import { Add } from lib;"]
    "return a0 + 1;" ["meets Add"] lib
  expectRefused "the trait and implementation behind a plain import" ["import lib;"]
    "return a0 + 1;" ["meets Add"] lib
  expectRefused "the trait not exported, behind a plain import" ["import lib;"]
    "return a0 + 1;" ["meets Add"]
    [("lib.solc", ["export { f };", addTrait, addFirst,
      "function f(x: word) returns (word) { return x; }"])]
  expectRefused "the trait two imports away" ["import mid;"] "return a0 + 1;" ["meets Add"]
    [("mid.solc", ["import lib;", "export { g };", "function g(x: word) returns (word) { return x; }"]),
      ("lib.solc", ["export { Add };", addTrait, addFirst])]
  let plus := ("lib.solc", ["export { Plus };",
    "trait Plus<a> { function add(x: a, y: a) returns (a); }",
    "impl Plus<word> { function add(x: word, y: word) returns (word) { return x; } }"])
  expectRefused "a trait imported as Add" ["import { Plus as Add } from lib;"] "return a0 + 1;"
    ["meets Add"] [plus]
  expectRefused "a trait imported as Add one import further" ["import mid;"] "return a0 + 1;"
    ["meets Add"]
    [("mid.solc", ["import { Plus as Add } from lib;", "export { g };",
      "function g(x: word) returns (word) { return x; }"]), plus]
  expectRefused "Add imported as Plus" ["import { Add as Plus } from lib;"] "return a0 + 1;"
    ["meets Add"] lib
  expectRefused "Add imported as Plus one import further" ["import mid;"] "return a0 + 1;"
    ["meets Add"]
    [("mid.solc", ["import { Add as Plus } from lib;", "export { g };",
      "function g(x: word) returns (word) { return x; }"]),
      ("lib.solc", ["export { Add };", addTrait, addFirst])]

/-- `Shl` and `Shr` implementations at a builtin type, refused where they are declared. -/
private def testRefusedShifts : IO Unit := do
  expectRefused "Shl at word" [shlTrait,
    "impl Shl<word, word> { function bshl(x: word, y: word) returns (word) { return 5; } }"]
    "return a0 << 2;" ["shift"]
  expectRefused "Shl at word, unused" [shlTrait,
    "impl Shl<word, word> { function bshl(x: word, y: word) returns (word) { return 5; } }"]
    "return a0;" ["shift"]
  expectRefused "Shr at uint8" ["trait Shr<a, b> { function bshr(x: a, y: b) returns (a); }",
    "impl Shr<uint8, word> { function bshr(x: uint8, y: word) returns (uint8) { return x; } }"]
    "return a0 >> 1;" ["shift"]

/-- Programs the rule leaves: generic code, traits without the operator's method, and types
where Lean has no builtin. -/
private def testAccepted : IO Unit := do
  expectResults "the generic use at word" [addTrait, addFirst,
    "function twice<t>(x: t) returns (t) where t: Add { return x + x; }"]
    "return twice(a0);" [9, maximum]
  expectResults "Sub through generic code" ["trait Sub<a> { function sub(x: a, y: a) returns (a); }",
    "impl Sub<word> { function sub(x: word, y: word) returns (word) { return 5; } }",
    "function g<t>(x: t, y: t) returns (t) where t: Sub { return x - y; }"]
    "return g(a0, 2);" [5, 5]
  expectResults "Eq through generic code" [eqTrait,
    "impl Eq<word> { function eq(x: word, y: word) returns (bool) { return true; } }",
    "function g<t>(x: t, y: t) returns (bool) where t: Eq { return x == y; }"]
    (condition "g(a0, 2)") [1, 1]
  expectResults "BitNot through generic code" [bitNotTrait,
    "impl BitNot<word> { function bnot(x: word) returns (word) { return 5; } }",
    "function g<t>(x: t) returns (t) where t: BitNot { return ~x; }"]
    "return g(a0);" [5, 5]
  expectResults "UncheckedAdd through generic code" [
    "trait UncheckedAdd<a> { function add(x: a, y: a) returns (a); }",
    "impl UncheckedAdd<word> { function add(x: word, y: word) returns (word) { return 5; } }",
    "function g<t>(x: t, y: t) returns (t) where t: UncheckedAdd { unchecked { return x + y; } }"]
    "return g(a0, 2);" [5, 5]
  expectResults "Eq at bool" [eqTrait,
    "impl Eq<bool> { function eq(x: bool, y: bool) returns (bool) { return true; } }"]
    (condition "true == false") [1, 1]
  expectResults "BitAnd at bool" ["trait BitAnd<a> { function band(x: a, y: a) returns (a); }",
    "impl BitAnd<bool> { function band(x: bool, y: bool) returns (bool) { return true; } }"]
    (condition "true & false") [1, 1]
  expectResults "Add at a program's own type" ([addTrait] ++ box ++
    ["impl Add<Box> { function add(x: Box, y: Box) returns (Box) { return x; } }"])
    "return unbox(Box(4) + Box(5));" [4, 4]
  expectResults "Shl at a program's own type" ([shlTrait] ++ box ++
    ["impl Shl<Box, word> { function bshl(x: Box, y: word) returns (Box) { return x; } }"])
    "return a0;" [9, maximum]
  expectResults "a marker Eq without eq" ["trait Eq<a> {}", "impl Eq<word> {}"]
    (condition "a0 == 9") [1, 0]
  expectResults "an Add whose method is plus" ["trait Add<a> { function plus(x: a, y: a) returns (a); }",
    "impl Add<word> { function plus(x: word, y: word) returns (word) { return 7; } }"]
    "return 1 + 2;" [3, 3]
  expectResults "a Shl whose method is not bshl" [
    "trait Shl<a, b> { function shift(x: a, y: b) returns (a); }",
    "impl Shl<word, word> { function shift(x: word, y: word) returns (word) { return 5; } }"]
    "return a0 << 2;" [36, maximum - 3]

/-- An operator's trait by its declared name, in generic code (AL02, AL04, AL06 and AL08): an import
alias gives a trait a second name, not a second meaning. -/
private def testDeclaredName : IO Unit := do
  let plus := ("lib.solc", ["export { Plus };",
    "trait Plus<a> { function add(x: a, y: a) returns (a); }",
    "impl Plus<word> { function add(x: word, y: word) returns (word) { return x; } }"])
  let add := ("lib.solc", ["export { Add };", addTrait, addFirst])
  let twice (trait : String) : String :=
    s!"function twice<t>(x: t) returns (t) where t: {trait} \{ return x + x; }"
  expectRefused "Plus imported as Add, in generic code" ["import { Plus as Add } from lib;", twice "Add"]
    "return twice(a0);" ["inference"] [plus]
  expectResults "Add imported as Plus, in generic code" ["import { Add as Plus } from lib;", twice "Plus"]
    "return twice(a0);" [9, maximum] [add]
  expectRefused "Plus imported as Add, in generic code one import further" ["import { twice } from mid;"]
    "return twice(a0);" ["inference"]
    [("mid.solc", ["import { Plus as Add } from lib;", "export { twice };", twice "Add"]), plus]
  expectResults "Add imported as Plus, in generic code one import further" ["import { twice } from mid;"]
    "return twice(a0);" [9, maximum]
    [("mid.solc", ["import { Add as Plus } from lib;", "export { twice };", twice "Plus"]), add]

def run : IO Unit := do
  testRefusedUses
  testRefusedShifts
  testAccepted
  testDeclaredName
  IO.println "operators beside a program's implementation: the use-site rule GREEN"

end Tests.OperatorImplementations
