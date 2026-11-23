import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.ProgramImports

/-! Upstream's import rules at the whole-program load: a selected or wildcard import beside a
declaration of the importing module (`SC0108`), an unknown selected or hidden item (`SC0110`) and
an unknown module are refused where they are; an import of one of upstream's std modules is not,
and the rules count the names it exports with their namespaces (`upstreamStandardModuleExports`);
of two import declarations that bind one name from one module, the first is kept; a name listed
twice in one import (`SC0117`), a name brought from two modules (`SC0120`) and a qualifier beside a
value (`SC0121`) are refused, and so are two imports under one qualifier (`SC0116`); the export
checks refuse a local export that names nothing the module declares or imports (`SC0113`), a
constructor its type does not show (`SC0114`), a re-export that its module does not export
(`SC0115`), std's modules by their export tables, std types by the constructors they show, one
public name for items of two origins (`SC0111`), std's names by the modules that declare them,
and one public name for two modules (`SC0112`); a std name that a user module re-exports binds on
through its importers, `std.opcodes`' functions to their builtins; and a module that no import or
re-export reaches from the entry is not checked, as upstream validates only the reachable ones.
Each case is a source that upstream's pinned checker was probed with, and gives upstream's
answer. -/

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
  | .unknownExportName _ name => s!"export {name}"
  | .unknownExportConstructor _ typeName constructorName =>
      s!"constructor {typeName}.{constructorName}"
  | .duplicateImportQualifier _ name => s!"qualifier twice {name}"
  | .duplicateExportName _ name => s!"exported twice {name}"
  | .duplicateExportModule _ name => s!"exported module twice {name}"
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

private def checks (imports : List String) (body : String)
    (loose : List Workspace.RawSourceFile := []) : Bool :=
  match checkProgram (workspace imports [] body loose) with
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

/-- Modules beside std's: one exporting a function named like std's `not`, one a function named like
std's constructor `Empty`, and a module whose path ends in a name std exports as a function. -/
private def standardNeighbours : List Workspace.RawSourceFile := [
  { path := "lib8.solc", content :=
      "pragma solcore;\nexport { not };\nfunction not(x: word) returns (word) { return x; }" },
  { path := "lib9.solc", content :=
      "pragma solcore;\nexport { Empty };\nfunction Empty(x: word) returns (word) { return x; }" },
  { path := "pkg/lt.solc", content :=
      "pragma solcore;\nexport { g };\nfunction g(x: word) returns (word) { return x; }" }]

/-- The rules with std's modules other than `std.opcodes`, by the names they export and their
namespaces: a constructor is no item (`SC0110`) and meets nothing; a function meets a value, and a
type or a trait a type, an enum or a trait (`SC0108`); a name std and another module bring is
ambiguous, a re-export beside its origin too (`SC0120`); and a std function meets a qualifier
(`SC0121`). -/
private def testStandardModules : IO Unit := do
  let lt := "function lt(x: word, y: word) returns (word) { return x; }"
  expectRefused "unknown item of std" ["import { nosuch } from std;"] [] ["item nosuch"]
  expectRefused "unknown hidden item of std" ["import * from std hiding { nosuch };"] []
    ["item nosuch"]
  expectRefused "a constructor of std selected" ["import { Empty } from std;"] [] ["item Empty"]
  expectLoaded "a type of std selected" ["import { Error } from std;"] []
  expectRefused "std wildcard, a local function of a std function's name" ["import * from std;"]
    [lt] ["value lt"]
  expectRefused "a std trait selected, a local trait" ["import { Add } from std;"]
    ["trait Add<a> {}"] ["type Add"]
  expectRefused "std wildcard, a local enum named like a std type" ["import * from std;"]
    ["enum DynArray { D }"] ["type DynArray"]
  expectLoaded "std wildcard, a local function named like a std trait" ["import * from std;"]
    ["function Add(x: word) returns (word) { return x; }"]
  expectLoaded "std wildcard, a local function named like a std type" ["import * from std;"]
    ["function DynArray(x: word) returns (word) { return x; }"]
  expectLoaded "std wildcard, a local function named like a std constructor" ["import * from std;"]
    ["function Empty(x: word) returns (word) { return x; }"]
  expectLoaded "a std function hidden, a local of its name" ["import * from std hiding { lt };"]
    [lt]
  expectRefused "std and std.opcodes wildcards"
    ["import * from std;", "import * from std.opcodes;"] []
    (["addmod", "address", "and", "byte", "gt", "log1", "lt", "mulmod", "not", "or"].map
      ("ambiguous " ++ ·))
  expectLoaded "std, std.opcodes hiding the ten it shares"
    ["import * from std;",
      "import * from std.opcodes hiding { addmod, address, and, byte, gt, " ++
        "log1, lt, mulmod, not, or };"]
    []
  expectRefused "std wildcard, a selected std.opcodes type-named function"
    ["import * from std;", "import { address } from std.opcodes;"] [] ["ambiguous address"]
  expectRefused "one function from std and std.opcodes"
    ["import { lt } from std;", "import { lt } from std.opcodes;"] [] ["ambiguous lt"]
  expectLoaded "std hiding not, not from std.opcodes"
    ["import * from std hiding { not };", "import { not } from std.opcodes;"] []
  expectLoaded "std and an alias from std.opcodes"
    ["import * from std;", "import { not as n } from std.opcodes;"] []
  expectRefused "std and a user module sharing a function"
    ["import * from std;", "import * from lib8;"] [] ["ambiguous not"] (loose := standardNeighbours)
  expectLoaded "std's constructor and a user module's function of its name"
    ["import * from std;", "import * from lib9;"] [] (loose := standardNeighbours)
  expectRefused "a re-export of std beside its origin"
    ["import * from std.unchecked.signed;", "import * from std.unchecked.unsigned;"] []
    (["UncheckedAdd", "UncheckedSub", "UncheckedMul", "UncheckedDiv", "UncheckedMod"].map
      ("ambiguous " ++ ·))
  expectLoaded "std twice, std beside std.dispatch, std.signed beside std.opcodes"
    ["import * from std;", "import * from std;", "import * from std.dispatch;",
      "import * from std.signed;"] []
  expectRefused "a plain import's qualifier beside a std function"
    ["import pkg.lt;", "import * from std;"] [] ["qualifier lt"] (loose := standardNeighbours)

/-- Modules for the export checks: a type with its constructors shown, a module that imports a
function and does not export it, an unknown export reached by a plain import or a re-export, an
unknown re-export, an unknown exported constructor, and two cycles of re-exports, one without the
name. -/
private def exportNeighbours : List Workspace.RawSourceFile := [
  { path := "shown.solc", content := String.intercalate "\n" ["pragma solcore;",
      "export { Color(*), f };", "enum Color { Red, Green }", localF] },
  { path := "kept.solc", content := "pragma solcore;\nimport { f } from lib;" },
  { path := "bad.solc", content := "pragma solcore;\nexport { f, nosuch };\n" ++ localF },
  { path := "relay.solc", content := "pragma solcore;\nexport bad.*;" },
  { path := "badre.solc", content := "pragma solcore;\nexport lib.{ f, nosuch };" },
  { path := "badc.solc", content := "pragma solcore;\nexport { E(A, C) };\nenum E { A, B }" },
  { path := "ca.solc", content := "pragma solcore;\nexport cb.{ f };" },
  { path := "cb.solc", content := "pragma solcore;\nexport ca.{ f };" },
  { path := "da.solc", content := "pragma solcore;\nexport db.{ f };" },
  { path := "db.solc", content := "pragma solcore;\nexport lib.{ f };\nexport da.*;" }]

/-- `SC0113`: a local export names a declaration of the module or a name a selected or wildcard
import brings, under its alias, and not a constructor, a qualifier or a hidden name; with a
constructor selection, a data type. A module is checked where an import or a re-export reaches
it. -/
private def testLocalExports : IO Unit := do
  expectRefused "an unknown export" [] ["export { nosuch };"] ["export nosuch"]
  expectRefused "a declaration and an unknown export" [] ["export { run, nosuch };"]
    ["export nosuch"]
  expectLoaded "a selected import's name, and a wildcard import's" ["import { f } from lib;"]
    ["export { f };"]
  expectLoaded "a wildcard import's name" ["import * from lib;"] ["export { f };"]
  expectRefused "a hidden name" ["import * from lib hiding { f };"] ["export { f };"] ["export f"]
  expectLoaded "a selected alias" ["import { f as g } from lib;"] ["export { g };"]
  expectRefused "an alias's original name" ["import { f as g } from lib;"] ["export { f };"]
    ["export f"]
  expectRefused "a plain import's qualifier" ["import lib;"] ["export { lib };"] ["export lib"]
  expectRefused "a namespace import's alias" ["import * as L from lib;"] ["export { L };"]
    ["export L"]
  expectRefused "a constructor alone" [] ["enum E { A, B }", "export { A };"] ["export A"]
  expectRefused "a function with a constructor selection" [] ["export { run(A) };"]
    ["export run"]
  expectRefused "a type alias with all constructors" [] ["type TT = word;", "export { TT(*) };"]
    ["export TT"]
  expectLoaded "a trait, the module's wildcard and a module's" []
    ["trait Tr<a> { function m(x: a) returns (a); }", "export { Tr };", "export { * };",
      "export { lib.* };"]
  expectLoaded "one name twice" [] ["export { run, run };"]
  expectRefused "an unknown export in a plain-imported module" ["import bad;"] [] ["export nosuch"]
    (loose := exportNeighbours)
  expectRefused "an unknown export reached through a re-export" ["import relay;"] []
    ["export nosuch"] (loose := exportNeighbours)
  expectLoaded "an unknown export in an unreachable module" [] [] (loose := exportNeighbours)

/-- `SC0114`: an exported constructor of a local type, or of an imported one that shows it; a
constructor selection on an imported type that shows none names none. -/
private def testExportedConstructors : IO Unit := do
  expectRefused "a local enum, an unknown constructor" [] ["enum E { A, B }", "export { E(A, C) };"]
    ["constructor E.C"]
  expectLoaded "a local enum: all, one twice, and two exports" []
    ["enum E { A, B }", "export { E(*) };", "export { E(A, A) };", "export { E(B) };"]
  expectRefused "another type's constructor" [] ["enum E { A }", "enum F { B }", "export { E(B) };"]
    ["constructor E.B"]
  expectRefused "an opaque import, a constructor" ["import { Color } from lib;"]
    ["export { Color(Red) };"] ["constructor Color.Red"]
  expectLoaded "an opaque import, all constructors" ["import { Color } from lib;"]
    ["export { Color(*) };"]
  expectLoaded "a shown import, a constructor" ["import { Color } from shown;"]
    ["export { Color(Red) };"] (loose := exportNeighbours)
  expectRefused "a shown wildcard's type, an unknown constructor" ["import * from shown;"]
    ["export { Color(Red, Blue) };"] ["constructor Color.Blue"] (loose := exportNeighbours)
  expectRefused "an unknown constructor in a plain-imported module" ["import badc;"] []
    ["constructor E.C"] (loose := exportNeighbours)

/-- `SC0115`: a re-export names an item its module exports, through re-exports and their cycles,
and a constructor its type shows there; a constructor alone, and a name the module imports and does
not export, are none. -/
private def testReexports : IO Unit := do
  expectRefused "an unknown name" [] ["export lib.{ nosuch };"] ["export nosuch"]
  expectLoaded "a function" [] ["export lib.{ f };"]
  expectLoaded "a function through a module re-exporting all" [] ["export lib4.{ k };"]
  expectLoaded "a re-exported import" [] ["export lib3.{ f };"]
  expectRefused "an opaque type's constructor" [] ["export lib.{ Color(Red) };"]
    ["constructor Color.Red"]
  expectLoaded "a shown type's constructor" [] ["export shown.{ Color(Red) };"]
    (loose := exportNeighbours)
  expectRefused "a shown type's unknown constructor" [] ["export shown.{ Color(Blue) };"]
    ["constructor Color.Blue"] (loose := exportNeighbours)
  expectRefused "a function with a constructor selection" [] ["export lib.{ f(A) };"] ["export f"]
  expectRefused "a constructor alone" [] ["export shown.{ Red };"] ["export Red"]
    (loose := exportNeighbours)
  expectRefused "a name its module imports and does not export" [] ["export kept.{ f };"]
    ["export f"] (loose := exportNeighbours)
  expectRefused "a known and an unknown name" [] ["export lib.{ k, nosuch };"] ["export nosuch"]
  expectRefused "an unknown re-export in a plain-imported module" ["import badre;"] []
    ["export nosuch"] (loose := exportNeighbours)
  expectRefused "a cycle of re-exports without the name" ["import ca;"] []
    ["export f", "export f"] (loose := exportNeighbours)
  expectLoaded "a cycle of re-exports with the name" ["import { f } from da;"] []
    (loose := exportNeighbours)

/-- The export checks with upstream's std modules, by their export tables: a local export names a
function, a type or a trait that a selected or wildcard import of one binds, and a re-export one
that the module exports; a constructor selection is checked as no type's. -/
private def testStandardExports : IO Unit := do
  expectLoaded "a selected std.opcodes function" ["import { div } from std.opcodes;"]
    ["export { div };"]
  expectLoaded "a std.opcodes wildcard's function and an alias"
    ["import * from std.opcodes;", "import { mod as m } from std.opcodes;"] ["export { div, m };"]
  expectRefused "a hidden std.opcodes function" ["import * from std.opcodes hiding { div };"]
    ["export { div };"] ["export div"]
  expectRefused "a plain import of std.opcodes" ["import std.opcodes;"] ["export { div };"]
    ["export div"]
  expectLoaded "std's function, type and trait" ["import * from std;"]
    ["export { tobool, Error, Typedef };"]
  expectRefused "a std function with a constructor selection" ["import { tobool } from std;"]
    ["export { tobool(A) };"] ["export tobool"]
  expectRefused "a std name with no import" [] ["export { tobool };"] ["export tobool"]
  expectLoaded "a std type's constructors" ["import { Error } from std;"]
    ["export { Error(*) };", "export { Error(Empty) };"]
  expectLoaded "re-exports of std's names and modules" []
    ["export std.opcodes.{ div };", "export std.{ tobool, Error(Empty) };", "export std.opcodes.*;",
      "export std.opcodes;"]
  expectRefused "re-exports of names std does not export" []
    ["export std.opcodes.{ nosuch };", "export std.{ nosuch2 };"]
    ["export nosuch", "export nosuch2"]

private def coerce : String := "pragma solcore;\nexport { Coerce };\ntrait Coerce<From, To> {}"

/-- Modules for `SC0116` and `SC0111`: a root module and a nested one named like modules of the
workspace, a module with two plain imports of one module, and a module that re-exports two traits
of one name. -/
private def duplicateNeighbours : List Workspace.RawSourceFile := [
  { path := "mod.solc", content :=
      "pragma solcore;\nexport { h };\nfunction h(x: word) returns (word) { return x; }" },
  { path := "pkg/lib.solc", content :=
      "pragma solcore;\nexport { g };\nfunction g(x: word) returns (word) { return x; }" },
  { path := "dupq.solc", content := "pragma solcore;\nimport lib;\nimport lib;" },
  { path := "left.solc", content := coerce },
  { path := "right.solc", content := coerce },
  { path := "hub.solc", content := "pragma solcore;\nexport left.*;\nexport right.*;" }]

/-- `SC0116`: two plain or namespace imports under one qualifier, a namespace import's alias or a
plain import's last path component, whatever modules they name, std's among them; a selective or
wildcard import has none. -/
private def testDuplicateQualifiers : IO Unit := do
  expectRefused "one module plain-imported twice" ["import lib;", "import lib;"] []
    ["qualifier twice lib"]
  expectRefused "two modules with one last component" ["import lib;", "import pkg.lib;"] []
    ["qualifier twice lib"] (loose := duplicateNeighbours)
  expectRefused "two namespace imports under one alias"
    ["import * as L from lib;", "import * as L from lib2;"] [] ["qualifier twice L"]
  expectRefused "a namespace alias and a plain import's last component"
    ["import * as lib from lib2;", "import lib;"] [] ["qualifier twice lib"]
  expectLoaded "a plain import beside a selective import of its module"
    ["import lib;", "import { f } from lib;"] []
  expectLoaded "a namespace import beside a wildcard of its module"
    ["import * as L from lib;", "import * from lib;"] []
  expectLoaded "two namespace imports of one module under two aliases"
    ["import * as L from lib;", "import * as N from lib;"] []
  expectLoaded "a plain import beside a namespace alias of another name"
    ["import lib;", "import * as L from lib;"] []
  expectRefused "std.opcodes plain-imported twice" ["import std.opcodes;", "import std.opcodes;"]
    [] ["qualifier twice opcodes"]
  expectRefused "std plain-imported twice" ["import std;", "import std;"] [] ["qualifier twice std"]
  expectRefused "std.opcodes beside a namespace alias opcodes"
    ["import std.opcodes;", "import * as opcodes from lib;"] [] ["qualifier twice opcodes"]
  expectRefused "a nested module beside a root module of its last component"
    ["import pkg.mod;", "import mod;"] [] ["qualifier twice mod"] (loose := duplicateNeighbours)
  expectRefused "two qualifiers in a plain-imported module" ["import dupq;"] []
    ["qualifier twice lib"] (loose := duplicateNeighbours)
  expectLoaded "the same module, unreachable" [] [] (loose := duplicateNeighbours)

/-- `SC0111`: one public name that a module's exports give to items of two origins, each the
module that declares it and its name there, in any namespace; one item reached twice, a local type
and function of one name, and an alias beside its original are one origin or two names. -/
private def testDuplicateExports : IO Unit := do
  expectRefused "two functions exported under one name" ["import { f } from lib;"]
    ["export { f };", "export lib2.{ f };"] ["exported twice f"]
  expectLoaded "a local type and a local function of one name" []
    ["enum Hue { A }", "function Hue(x: word) returns (word) { return x; }", "export { Hue };"]
  expectRefused "a local function and another module's type of its name" []
    ["function Color(x: word) returns (word) { return x; }", "export { Color };",
      "export shown.{ Color };"] ["exported twice Color"] (loose := exportNeighbours)
  expectRefused "two modules' wildcards sharing a name" [] ["export lib2.*;", "export lib3.*;"]
    ["exported twice f"]
  expectLoaded "one item through its module and a relay" []
    ["export lib.{ f };", "export lib3.{ f };"]
  expectLoaded "an alias beside its original" ["import { f as g } from lib;"]
    ["export { g };", "export lib.{ f };"]
  expectLoaded "a selected import and a re-export of the same item" ["import { f } from lib;"]
    ["export { f };", "export lib.{ f };"]
  expectRefused "a module's wildcard beside a local of a name it exports" []
    [localF, "export { f };", "export lib.*;"] ["exported twice f"]
  expectLoaded "a std.opcodes function selected and re-exported"
    ["import { div } from std.opcodes;"] ["export { div };", "export std.opcodes.{ div };"]
  expectRefused "a module re-exporting two traits of one name, plain-imported" ["import hub;"] []
    ["exported twice Coerce"] (loose := duplicateNeighbours)
  expectLoaded "the same module, unreachable" [] [] (loose := duplicateNeighbours)

/-- Modules for `SC0112` and for the std names that user modules re-export: two module exports
under one name, relays of `std.opcodes`' `div` by a re-export, a selection, a wildcard and a
relay, of its `mload` and of std's `tobool`, and a user module's own `div`. -/
private def relayNeighbours : List Workspace.RawSourceFile := [
  { path := "twomods.solc", content := "pragma solcore;\nexport lib as M;\nexport lib2 as M;" },
  { path := "relaystd.solc", content := "pragma solcore;\nexport std.opcodes.{ div };" },
  { path := "relaysel.solc", content :=
      "pragma solcore;\nimport { div } from std.opcodes;\nexport { div };" },
  { path := "relaywild.solc", content := "pragma solcore;\nexport std.opcodes.*;" },
  { path := "relaytwice.solc", content := "pragma solcore;\nexport relaystd.{ div };" },
  { path := "relaym.solc", content := "pragma solcore;\nexport std.opcodes.{ mload };" },
  { path := "relaytb.solc", content := "pragma solcore;\nexport std.{ tobool };" },
  { path := "divlib.solc", content := String.intercalate "\n" ["pragma solcore;", "export { div };",
      "function div(x: word, y: word) returns (word) { return x; }"] }]

/-- `SC0112`: one public name that a module's module exports give to two modules, a std module
counting by its path; one module exported twice under one name or under two names, and a module
alias beside an item of its name, are none. -/
private def testDuplicateModuleExports : IO Unit := do
  expectRefused "two modules exported under one name" [] ["export lib as M;", "export lib2 as M;"]
    ["exported module twice M"]
  expectLoaded "one module exported twice under one name" []
    ["export lib as M;", "export lib as M;"]
  expectLoaded "one module under two names" [] ["export lib as M;", "export lib as N;"]
  expectRefused "a module by its name beside another under that name" []
    ["export lib;", "export lib2 as lib;"] ["exported module twice lib"]
  expectLoaded "a module by its name and by an alias of that name" []
    ["export lib;", "export lib as lib;"]
  expectRefused "std.opcodes and a user module under one name" []
    ["export std.opcodes as M;", "export lib as M;"] ["exported module twice M"]
  expectRefused "std and std.opcodes under one name" []
    ["export std as M;", "export std.opcodes as M;"] ["exported module twice M"]
  expectRefused "std.opcodes by its name beside a user module as opcodes" []
    ["export std.opcodes;", "export lib as opcodes;"] ["exported module twice opcodes"]
  expectLoaded "std.opcodes by its name and as opcodes" []
    ["export std.opcodes;", "export std.opcodes as opcodes;"]
  expectLoaded "a module alias beside an item of its name" []
    ["function M(x: word) returns (word) { return x; }", "export { M };", "export lib as M;"]
  expectRefused "two modules under one name in a plain-imported module" ["import twomods;"] []
    ["exported module twice M"] (loose := relayNeighbours)
  expectLoaded "the same module, unreachable" [] [] (loose := relayNeighbours)

/-- `SC0114` and `SC0115` for std types: a std type shows the constructors its std module's export
shows, all of a type's own for `T(*)` and none for an opaque type. -/
private def testStandardConstructors : IO Unit := do
  expectRefused "a std type's unknown constructor" ["import { Error } from std;"]
    ["export { Error(Nope) };"] ["constructor Error.Nope"]
  expectLoaded "a std type's constructors" ["import { Error } from std;"]
    ["export { Error(Empty, Msg) };"]
  expectRefused "a known and an unknown constructor" ["import { Error } from std;"]
    ["export { Error(Empty, Nope) };"] ["constructor Error.Nope"]
  expectRefused "an opaque std type's constructor" ["import { DynArray } from std;"]
    ["export { DynArray(Nope) };"] ["constructor DynArray.Nope"]
  expectLoaded "an opaque std type with all its constructors" ["import { DynArray } from std;"]
    ["export { DynArray(*) };"]
  expectLoaded "a std wildcard's type with a constructor" ["import * from std;"]
    ["export { Error(Msg) };"]
  expectRefused "a re-export of a std type's unknown constructor" [] ["export std.{ Error(Nope) };"]
    ["constructor Error.Nope"]
  expectRefused "a re-export of an opaque std type's constructor" []
    ["export std.{ DynArray(Nope) };"] ["constructor DynArray.Nope"]
  expectLoaded "re-exports of std types' constructors" []
    ["export std.{ Error(Error) };", "export std.{ DynArray(*) };"]
  expectRefused "a submodule's opaque type with a constructor" []
    ["export std.unsigned.{ uint8(uint8) };"] ["constructor uint8.uint8"]

/-- `SC0111` with std's names: a std name's origin is the std module that declares it and its name
there, so std's own `lt` and `std.opcodes`' are two, and so are a local function and std's of its
name; one std item exported twice is one. -/
private def testStandardOrigins : IO Unit := do
  let tobool := "function tobool(x: word) returns (word) { return x; }"
  expectRefused "one name re-exported from std and std.opcodes" []
    ["export std.{ lt };", "export std.opcodes.{ lt };"] ["exported twice lt"]
  expectRefused "a std.opcodes function and a user module's of its name"
    ["import { div } from std.opcodes;"] ["export { div };", "export divlib.{ div };"]
    ["exported twice div"] (loose := relayNeighbours)
  expectRefused "a local function and std's of its name" []
    [tobool, "export { tobool };", "export std.{ tobool };"] ["exported twice tobool"]
  expectRefused "a local function and std's wildcard" []
    [tobool, "export { tobool };", "export std.*;"] ["exported twice tobool"]
  expectLoaded "one std name re-exported twice" []
    ["export std.{ tobool };", "export std.{ tobool };"]
  expectLoaded "a std name selected and re-exported" ["import { tobool } from std;"]
    ["export { tobool };", "export std.{ tobool };"]
  expectRefused "an alias of std's name beside std.opcodes' of that name"
    ["import { tobool as lt } from std;"] ["export { lt };", "export std.opcodes.{ lt };"]
    ["exported twice lt"]
  let both := refusedImports [] ["export std.*;", "export std.opcodes.*;"]
  assertTrue (both.any fun errors => errors.contains "exported twice addmod")
    s!"std's and std.opcodes' wildcards: expected addmod twice, got {both}"

/-- The std names a user module re-exports bind on through its importers: `std.opcodes`' functions
to their builtins, through a re-export, a selection, a wildcard and a relay of a relay, selected,
aliased, through a wildcard import and named qualified. Std's other names bind nothing, so they are
refused where they are used, as an import of their module's are; so is an effectful function.
Beside a local of its name, a second module's import of it, or a direct import, the name is
refused, as upstream refuses it (`SC0108`, `SC0120`). -/
private def testRelayedStandardNames : IO Unit := do
  let relayed (imports : List String) (body : String) : Bool := checks imports body relayNeighbours
  assertTrue (relayed ["import { div } from relaystd;"] "div(x, 4)") "a relay's re-export, used"
  assertTrue (relayed ["import { div } from relaysel;"] "div(x, 4)") "a relay's selection, used"
  assertTrue (relayed ["import { div } from relaywild;"] "div(x, 4)") "a relay's wildcard, used"
  assertTrue (relayed ["import { div } from relaytwice;"] "div(x, 4)") "a relay of a relay, used"
  assertTrue (relayed ["import * from relaystd;"] "div(x, 4)") "a relay through a wildcard import"
  assertTrue (relayed ["import { div as d } from relaystd;"] "d(x, 4)") "a relay's function aliased"
  assertTrue (relayed ["import relaystd;"] "relaystd.div(x, 4)") "a relay's function qualified"
  expectLoaded "a relay's std name, unused" ["import { tobool } from relaytb;"] []
    (loose := relayNeighbours)
  assertTrue (!relayed ["import { tobool } from relaytb;"] "tobool(x) ? 1 : 0")
    "a relay's std name, used, was not refused"
  assertTrue (!relayed ["import { mload } from relaym;"] "mload(x)")
    "a relay's effectful std.opcodes function, used, was not refused"
  expectRefused "a relay's function beside a local of its name" ["import { div } from relaystd;"]
    ["function div(x: word, y: word) returns (word) { return x; }"] ["value div"]
    (loose := relayNeighbours)
  expectRefused "two relays of one function"
    ["import { div } from relaystd;", "import { div } from relaysel;"] [] ["ambiguous div"]
    (loose := relayNeighbours)
  expectRefused "a relay's function beside a user module's"
    ["import { div } from relaystd;", "import { div } from divlib;"] [] ["ambiguous div"]
    (loose := relayNeighbours)
  expectRefused "a relay's function beside a direct import of it"
    ["import { div } from relaystd;", "import { div } from std.opcodes;"] [] ["ambiguous div"]
    (loose := relayNeighbours)
  expectRefused "an unknown name from a relay" ["import { nosuch } from relaystd;"] []
    ["item nosuch"] (loose := relayNeighbours)

def testImportParity : IO Unit := do
  testImportedNameConflicts
  testUnknownImports
  testFirstBindingKept
  testDuplicateImportNames
  testAmbiguousImports
  testQualifierConflicts
  testUnreachableModules
  testStandardModules
  testLocalExports
  testExportedConstructors
  testReexports
  testStandardExports
  testDuplicateQualifiers
  testDuplicateExports
  testDuplicateModuleExports
  testStandardConstructors
  testStandardOrigins
  testRelayedStandardNames

end Tests.ImportParity
