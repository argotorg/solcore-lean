import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.ProgramImports

/-! Upstream's import rules at the whole-program load: a selected or wildcard import beside a
declaration of the importing module (`SC0108`), an unknown selected or hidden item (`SC0110`) and
an unknown module are refused where they are; an import of one of upstream's std modules is not;
of two import declarations that bind one name from one module, the first is kept; a name listed
twice in one import (`SC0117`), a name brought from two modules (`SC0120`) and a qualifier beside a
value (`SC0121`) are refused; and a module that no import or re-export reaches from the entry is
not checked, as upstream validates only the reachable ones. Each case is a source that upstream's
pinned checker was probed with, and gives upstream's answer. -/

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

/-- Modules for the rules of `SC0120` and `SC0121`: a re-export of `lib`'s `f`, a wildcard
re-export of `lib`, a function named like `lib`'s `Color`, a function and a type named `lib`, and a
nested module. -/
private def moreLibraries : List Workspace.RawSourceFile := [
  { path := "lib3.solc", content := "pragma solcore;\nimport { f } from lib;\nexport { f };" },
  { path := "lib4.solc", content := "pragma solcore;\nexport lib.*;" },
  { path := "lib5.solc", content :=
      "pragma solcore;\nexport { Color };\nfunction Color(x: word) returns (word) { return x; }" },
  { path := "lib6.solc", content :=
      "pragma solcore;\nexport { lib };\nfunction lib(x: word) returns (word) { return x; }" },
  { path := "lib7.solc", content := "pragma solcore;\nexport { lib };\nenum lib { L }" },
  { path := "pkg/mod.solc", content :=
      "pragma solcore;\nexport { g };\nfunction g(x: word) returns (word) { return x; }" }]

private def workspace (imports declarations : List String) (body := "x")
    (loose : List Workspace.RawSourceFile := []) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    { path := "main.solc", content := String.intercalate "\n" (["pragma solcore;"] ++ imports ++
        declarations ++ [s!"function run(x: word) returns (word) \{ return {body}; }"]) },
    { path := "lib.solc", content := library },
    { path := "lib2.solc", content := otherLibrary }] ++ moreLibraries ++ loose
  externalLibraries := []
}

private def describe : ProgramInterfaceError → String
  | .importedNameConflict _ .value name => s!"value {name}"
  | .importedNameConflict _ _ name => s!"type {name}"
  | .unknownImportName _ _ name => s!"item {name}"
  | .unknownModule _ components => s!"module {".".intercalate components}"
  | .duplicateImportName _ name => s!"duplicate {name}"
  | .ambiguousImport _ name _ => s!"ambiguous {name}"
  | .importQualifierConflict _ name => s!"qualifier {name}"
  | error => reprStr error

/-- What a load refuses at the imports, described; none when it loads, and `other` when it fails
for another reason. -/
private def refusedImports (imports declarations : List String)
    (loose : List Workspace.RawSourceFile := []) : Option (List String) :=
  match loadProgram (workspace imports declarations (loose := loose)) with
  | .ok _ => none
  | .error [.imports errors] => some (errors.map describe)
  | .error _ => some ["other"]

private def expectRefused (label : String) (imports declarations : List String)
    (expected : List String) (loose : List Workspace.RawSourceFile := []) : IO Unit := do
  let found := refusedImports imports declarations loose
  assertTrue (found == some expected) s!"{label}: expected {expected}, got {found}"

private def expectLoaded (label : String) (imports declarations : List String)
    (loose : List Workspace.RawSourceFile := []) : IO Unit := do
  let found := refusedImports imports declarations loose
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
upstream's `or_insert` keeps it; from two modules the name is refused (`testAmbiguousImports`). -/
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
  let sameItemTwice ← mainImports ["import { f } from lib;", "import { f } from lib;"]
  assertTrue (valueSources sameItemTwice "f" == ["lib.f"])
    s!"the same item twice: {valueSources sameItemTwice "f"}"

/-- `SC0117`: within one selective import, a source name twice or a local name twice, and within
one hiding clause, a name twice; it reads only the import, so an import of std is refused too. -/
private def testDuplicateImportNames : IO Unit := do
  expectRefused "one source twice" ["import { f, f } from lib;"] [] ["duplicate f"]
  expectRefused "one source, two locals" ["import { f, f as g } from lib;"] [] ["duplicate f"]
  expectRefused "one alias twice" ["import { f as h, k as h } from lib;"] [] ["duplicate h"]
  expectRefused "a source and an alias of its name" ["import { f, k as f } from lib;"] []
    ["duplicate f"]
  expectRefused "a wildcard hiding one name twice" ["import * from lib hiding { f, f };"] []
    ["duplicate f"]
  expectRefused "a selective import hiding one name twice" ["import { k } from lib hiding { f, f };"]
    [] ["duplicate f"]
  expectRefused "one source twice from std" ["import { tobool, tobool } from std;"] []
    ["duplicate tobool"]
  expectLoaded "two sources and two locals" ["import { f as g, k } from lib;"] []

/-- `SC0120`: a local name brought from two or more modules, used or not, in any import group: a
re-export beside its origin counts as two modules, and a type and a function of one name meet. Two
imports of one module, an alias that avoids the name and a hidden name do not. -/
private def testAmbiguousImports : IO Unit := do
  expectRefused "one name from two modules" ["import { f } from lib;", "import { f } from lib2;"] []
    ["ambiguous f"]
  expectRefused "one alias from two modules"
    ["import { f as h } from lib;", "import { f2 as h } from lib2;"] [] ["ambiguous h"]
  expectRefused "two wildcards sharing a name" ["import * from lib;", "import * from lib2;"] []
    ["ambiguous f"]
  expectRefused "a selective import beside another module's wildcard"
    ["import { f } from lib;", "import * from lib2;"] [] ["ambiguous f"]
  expectRefused "a re-export beside its origin" ["import { f } from lib;", "import { f } from lib3;"]
    [] ["ambiguous f"]
  expectRefused "a wildcard re-export beside its origin" ["import * from lib;", "import * from lib4;"]
    [] ["ambiguous f", "ambiguous k", "ambiguous Color", "ambiguous Show", "ambiguous Blue"]
  expectRefused "a type and a function of one name"
    ["import { Color } from lib;", "import { Color } from lib5;"] [] ["ambiguous Color"]
  expectRefused "an alias making the name" ["import { f as f2 } from lib;", "import { f2 } from lib2;"]
    [] ["ambiguous f2"]
  expectLoaded "the shared name hidden" ["import * from lib hiding { f };", "import * from lib2;"] []
  expectLoaded "a selective import beside its own module's wildcard"
    ["import { f } from lib;", "import * from lib;"] []
  expectLoaded "an alias avoiding the name" ["import { f as g } from lib;", "import { f } from lib2;"] []
  expectLoaded "two plain imports" ["import lib;", "import lib2;"] []

/-- `SC0121`: a plain import's last path component and the first component of its path, and a
namespace import's alias, beside a value of the module of that name, declared or imported, std
included; a type of that name does not meet it. -/
private def testQualifierConflicts : IO Unit := do
  let declared (name : String) := s!"function {name}(x: word) returns (word) \{ return x; }"
  expectRefused "a plain import, a local of its name" ["import lib;"] [declared "lib"] ["qualifier lib"]
  expectRefused "a plain import, an imported function of its name"
    ["import lib;", "import { lib } from lib6;"] [] ["qualifier lib"]
  expectRefused "a namespace import, a local of its alias" ["import * as L from lib;"] [declared "L"]
    ["qualifier L"]
  expectRefused "a nested plain import, a local of its first component" ["import pkg.mod;"]
    [declared "pkg"] ["qualifier pkg"]
  expectRefused "a nested plain import, a local of its last component" ["import pkg.mod;"]
    [declared "mod"] ["qualifier mod"]
  expectRefused "a plain import of std, a local of its name" ["import std;"] [declared "std"]
    ["qualifier std"]
  expectRefused "a namespace import, an imported function of its alias"
    ["import * as lib from lib2;", "import { lib } from lib6;"] [] ["qualifier lib"]
  expectLoaded "a plain import, a local type of its name" ["import lib;"] ["enum lib { L }"]
  expectLoaded "a plain import, an imported type of its name"
    ["import lib;", "import { lib } from lib7;"] []
  expectLoaded "a namespace import, a local of the module's name" ["import * as L from lib;"]
    [declared "lib"]

/-- A module that no import or re-export reaches from the entry is not checked, as upstream
validates only the reachable ones; once main imports it, it is. -/
private def testUnreachableModules : IO Unit := do
  let loose : List Workspace.RawSourceFile := [
    { path := "loose.solc", content := String.intercalate "\n" ["pragma solcore;",
        "import { f } from lib;", "import { k, k } from lib;", "import { nosuch } from lib;",
        "import * from lib2;", "import { g } from nosuchmodule;",
        "function f(x: word) returns (word) { return x; }"] }]
  expectLoaded "an unreachable module with import errors" [] [] loose
  expectRefused "the same module, imported" ["import { f as h } from loose;"] []
    ["item nosuch", "module nosuchmodule", "item f", "value f", "duplicate k", "ambiguous f"] loose

def testImportParity : IO Unit := do
  testImportedNameConflicts
  testUnknownImports
  testFirstBindingKept
  testDuplicateImportNames
  testAmbiguousImports
  testQualifierConflicts
  testUnreachableModules

end Tests.ImportParity
