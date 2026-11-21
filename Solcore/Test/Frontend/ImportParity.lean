import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.ProgramImports

/-! Upstream's import rules at the whole-program load: a selected or wildcard import beside a
declaration of the importing module (`SC0108`), an unknown selected or hidden item (`SC0110`) and
an unknown module are refused where they are; an import of one of upstream's std modules is not;
and of two import declarations that bind one name from one module, the first is kept. Each case is
a source that upstream's pinned checker was probed with, and gives upstream's answer. -/

set_option autoImplicit false

namespace Tests.ImportParity

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def library : String := String.intercalate "\n" [
  "pragma solcore;",
  "export { f, k, Color, Show, Blue };",
  "function f(x: word) returns (word) { return x; }",
  "function k(x: word, y: word) returns (word) { return y; }",
  "function Blue(x: word) returns (word) { return x; }",
  "enum Color { Red, Green }",
  "trait Show<a> { function show(x: a) returns (word); }"]

private def otherLibrary : String := String.intercalate "\n" [
  "pragma solcore;",
  "export { f, f2 };",
  "function f(x: word) returns (word) { return x; }",
  "function f2(x: word) returns (word) { return x; }"]

private def workspace (imports declarations : List String) (body := "x") :
    Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    { path := "main.solc", content := String.intercalate "\n" (["pragma solcore;"] ++ imports ++
        declarations ++ [s!"function run(x: word) returns (word) \{ return {body}; }"]) },
    { path := "lib.solc", content := library },
    { path := "lib2.solc", content := otherLibrary }]
  externalLibraries := []
}

private def describe : ProgramInterfaceError → String
  | .importedNameConflict _ .value name => s!"value {name}"
  | .importedNameConflict _ _ name => s!"type {name}"
  | .unknownImportName _ _ name => s!"item {name}"
  | .unknownModule _ components => s!"module {".".intercalate components}"
  | error => reprStr error

/-- What a load refuses at the imports, described; none when it loads, and `other` when it fails
for another reason. -/
private def refusedImports (imports declarations : List String) : Option (List String) :=
  match loadProgram (workspace imports declarations) with
  | .ok _ => none
  | .error [.imports errors] => some (errors.map describe)
  | .error _ => some ["other"]

private def expectRefused (label : String) (imports declarations : List String)
    (expected : List String) : IO Unit := do
  let found := refusedImports imports declarations
  assertTrue (found == some expected) s!"{label}: expected {expected}, got {found}"

private def expectLoaded (label : String) (imports declarations : List String) : IO Unit := do
  let found := refusedImports imports declarations
  assertTrue found.isNone s!"{label}: expected a load, got {found}"

private def localF : String := "function f(x: word) returns (word) { return x; }"

/-- `SC0108`: values meet values, and types, enums, contracts and traits meet each other; hidden
names and constructors meet nothing, and an alias meets by its own name. -/
private def testImportedNameConflicts : IO Unit := do
  expectRefused "selected value" ["import { f } from lib;"] [localF] ["value f"]
  expectRefused "wildcard value" ["import * from lib;"] [localF] ["value f"]
  expectRefused "selected type, local enum" ["import { Color } from lib;"]
    ["enum Color { Blue2 }"] ["type Color"]
  expectRefused "selected trait, local enum" ["import { Show } from lib;"] ["enum Show { S }"]
    ["type Show"]
  expectRefused "selected type, local trait" ["import { Color } from lib;"]
    ["trait Color<a> { function c(x: a) returns (word); }"] ["type Color"]
  expectRefused "selected type, local contract" ["import { Color } from lib;"]
    ["contract Color { }"] ["type Color"]
  expectRefused "selected type, local type alias" ["import { Color } from lib;"]
    ["type Color = word;"] ["type Color"]
  expectRefused "wildcard trait, local type alias" ["import * from lib;"] ["type Show = word;"]
    ["type Show"]
  expectRefused "alias, local of the alias's name" ["import { f as g } from lib;"]
    ["function g(x: word) returns (word) { return x; }"] ["value g"]
  expectLoaded "wildcard hiding the name" ["import * from lib hiding { f };"] [localF]
  expectLoaded "selected value, local constructor" ["import { Blue } from lib;"]
    ["enum Tone { Blue }"]
  expectLoaded "selected type, local function named like its constructor"
    ["import { Color } from lib;"] ["function Red(x: word) returns (word) { return x; }"]
  expectLoaded "alias, local of the original name" ["import { f as g } from lib;"] [localF]
  expectLoaded "selected value, local contract" ["import { f } from lib;"] ["contract f { }"]
  expectLoaded "the same item twice" ["import { f } from lib;", "import { f } from lib;"] []
  expectLoaded "selected and hidden" ["import { f } from lib hiding { f };"] []

/-- `SC0110` and unknown modules, where the import is, even with no name resolved through it; and
upstream's std modules, which Lean lacks, accepted where they are. -/
private def testUnknownImports : IO Unit := do
  expectRefused "unknown selected item" ["import { nosuch } from lib;"] [] ["item nosuch"]
  expectRefused "unknown hidden item" ["import * from lib hiding { nosuch };"] [] ["item nosuch"]
  expectRefused "a constructor selected" ["import { Red } from lib;"] [] ["item Red"]
  expectRefused "unknown module" ["import { f } from nosuchmodule;"] [] ["module nosuchmodule"]
  expectRefused "unknown std module" ["import * from std.nosuch;"] [] ["module std.nosuch"]
  expectLoaded "std" ["import * from std;"] []
  expectLoaded "std.opcodes" ["import { div as sc_div } from std.opcodes;"] []
  expectLoaded "std.unchecked.signed" ["import * from std.unchecked.signed;"] []
  expectLoaded "a std module beside a local declaration" ["import * from std;"] [localF]

private def mainImports (imports : List String) : IO ProgramImports := do
  match loadProgram (workspace imports []) with
  | .error errors => throw (IO.userError s!"load failed: {reprStr errors}")
  | .ok loaded =>
      match loaded.environment.modules.find? fun module =>
          module.id.path.segments.map (·.text) == ["main"] with
      | none => throw (IO.userError "no main module")
      | some module =>
          match buildProgramImports loaded.environment module.id with
          | .error errors => throw (IO.userError s!"imports failed: {reprStr errors}")
          | .ok visibility => pure visibility

private def valueSources (visibility : ProgramImports) (name : String) : List String :=
  (visibility.valuesNamed name).map fun declaration =>
    let module := ".".intercalate (declaration.id.moduleId.path.segments.map (·.text))
    s!"{module}.{declaration.name.getD ""}"

private def checks (imports : List String) (body : String) : Bool :=
  match checkProgram (workspace imports [] body) with
  | .ok _ => true
  | .error _ => false

/-- Of two import declarations that bind one name from one module, the first is kept, as
upstream's `or_insert` keeps it; from two modules the name stays ambiguous (upstream's `SC0120`). -/
private def testFirstBindingKept : IO Unit := do
  let twoAliases ← mainImports ["import { f as h } from lib;", "import { k as h } from lib;"]
  assertTrue (valueSources twoAliases "h" == ["lib.f"])
    s!"two aliases: {valueSources twoAliases "h"}"
  assertTrue (checks ["import { f as h } from lib;", "import { k as h } from lib;"] "h(x)")
    "the first binding does not check"
  assertTrue (!checks ["import { f as h } from lib;", "import { k as h } from lib;"] "h(x, 1)")
    "the second binding still checks"
  let wildcardFirst ← mainImports ["import * from lib;", "import { k as f } from lib;"]
  assertTrue (valueSources wildcardFirst "f" == ["lib.f"])
    s!"wildcard first: {valueSources wildcardFirst "f"}"
  let selectedFirst ← mainImports ["import { k as f } from lib;", "import * from lib;"]
  assertTrue (valueSources selectedFirst "f" == ["lib.k"])
    s!"selected first: {valueSources selectedFirst "f"}"
  let twoModules ← mainImports ["import { f as h } from lib;", "import { f2 as h } from lib2;"]
  assertTrue (valueSources twoModules "h" == ["lib.f", "lib2.f2"])
    s!"two modules: {valueSources twoModules "h"}"
  let oneDeclaration ← mainImports ["import { f as h, k as h } from lib;"]
  assertTrue (valueSources oneDeclaration "h" == ["lib.f", "lib.k"])
    s!"one declaration: {valueSources oneDeclaration "h"}"

def testImportParity : IO Unit := do
  testImportedNameConflicts
  testUnknownImports
  testFirstBindingKept

end Tests.ImportParity
