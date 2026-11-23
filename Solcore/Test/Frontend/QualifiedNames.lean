import Solcore.Frontend.SourceCompiler

/-!
# Qualified names of user modules

A function of an imported module named qualified as a value is the reference its unqualified name
gives, as upstream resolves a qualified name in a value as in a callee: through a plain or
namespace import, a module alias, a wildcard or selected re-export and a nested import's last
component, at a typed or untyped local, generic at a typed local, and passed to a generic function
(`testValues`). A plain import of a nested path names its module by its last component and by the
full path it is seen by, a leading `lib` dropped, in calls, values, types, constructors and
patterns, and under the full path a module alias of the module (`testFullPaths`). Each case is a
source upstream's pinned checker was probed with, and gives upstream's verdict; an accepted one
runs at 9 and 2^256 − 1 and gives the results upstream's checked Hull gives.
-/

set_option autoImplicit false

namespace Tests.QualifiedNames

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def maximum : Nat := 2 ^ 256 - 1

private def libraries : List Workspace.RawSourceFile := [
  { path := "lib.solc", content := String.intercalate "\n" [
      "pragma solcore;",
      "export { add, f, k, id, Color(*) };",
      "function add(x: word, y: word) returns (word) { return y; }",
      "function f(x: word) returns (word) { return x; }",
      "function k(x: word, y: word) returns (word) { return x; }",
      "function id<t>(x: t) returns (t) { return x; }",
      "function hidden(x: word) returns (word) { return x; }",
      "enum Color { Red, Green }"] },
  { path := "lib3.solc", content := "pragma solcore;\nimport { f } from lib;\nexport { f };" },
  { path := "lib4.solc", content := "pragma solcore;\nexport lib.*;" },
  { path := "lib5.solc", content := "pragma solcore;\nexport lib;" },
  { path := "relay.solc", content := "pragma solcore;\nexport lib as L;" },
  { path := "relaystd.solc", content := "pragma solcore;\nexport std.opcodes.{ div };" },
  { path := "pkg/mod.solc", content := String.intercalate "\n" [
      "pragma solcore;",
      "export { g, T, Shape(*), toWord };",
      "function g(x: word) returns (word) { return x; }",
      "type T = word;",
      "enum Shape { Dot, Line }",
      "function toWord(s: Shape) returns (word) {",
      "  match (s) { case Shape.Dot { return 1; } case Shape.Line { return 2; } }",
      "}"] },
  { path := "pkg/lt.solc", content :=
      "pragma solcore;\nexport { g };\nfunction g(x: word) returns (word) { return 7; }" },
  { path := "pkg/relay.solc", content := "pragma solcore;\nexport lib.lib as L;" },
  { path := "a/b/c.solc", content :=
      "pragma solcore;\nexport { g };\nfunction g(x: word) returns (word) { return x; }" },
  { path := "other/mod.solc", content :=
      "pragma solcore;\nexport { g };\nfunction g(x: word) returns (word) { return 5; }" }]

/-- A module named like the directory `pkg`. -/
private def pkgModule : List Workspace.RawSourceFile := [
  { path := "pkg.solc", content :=
      "pragma solcore;\nexport { h };\nfunction h(x: word) returns (word) { return 3; }" }]

/-- A body that starts with `{` is `main`'s statements, any other the expression it returns. -/
private def workspace (imports declarations : List String) (body : String)
    (modules : List Workspace.RawSourceFile := []) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    { path := "main.solc", content := String.intercalate "\n" (["pragma solcore;"] ++ imports ++
        declarations ++ [s!"function main(a0: word) returns (word) " ++
          (if body.startsWith "{" then body else s!"\{ return {body}; }")]) }] ++ libraries ++
    modules
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

private def expectResults (label : String) (imports declarations : List String) (body : String)
    (expected : List Nat) (modules : List Workspace.RawSourceFile := []) : IO Unit := do
  let found ← runMain (workspace imports declarations body modules) [9, maximum]
  assertTrue (match found with | .ok results => results == expected | .error _ => false)
    s!"{label}: expected {expected}, got {reprStr found}"

private def expectRefused (label : String) (imports declarations : List String) (body : String)
    (stage : String) : IO Unit := do
  let found ← runMain (workspace imports declarations body) [9]
  assertTrue (match found with | .error refused => refused == stage | .ok _ => false)
    s!"{label}: expected a refusal at {stage}, got {reprStr found}"

private def apply : String :=
  "function apply(g: function (word, word) returns (word), x: word) returns (word) { return g(x, 4); }"

private def apply1 : String :=
  "function apply1(g: function (word) returns (word), x: word) returns (word) { return g(x); }"

private def twice : String :=
  "function twice<t>(g: function (t) returns (t), x: t) returns (t) { return g(g(x)); }"

/-- A function named qualified as a value, accepted with upstream's results, and the forms
upstream refuses: a value at the wrong type, a name the module does not export, a local named like
the qualifier, a module not imported or only selected from, and a type. -/
private def testValues : IO Unit := do
  let same := [9, maximum]
  expectResults "a plain import" ["import lib;"] [apply] "apply(lib.add, a0)" [4, 4]
  expectResults "a namespace import" ["import * as L from lib;"] [apply] "apply(L.add, a0)" [4, 4]
  expectResults "at a typed local" ["import lib;"] []
    "{ let g: function (word, word) returns (word) = lib.add; return g(a0, 4); }" [4, 4]
  expectResults "at an untyped local" ["import lib;"] [] "{ let g = lib.add; return g(a0, 4); }"
    [4, 4]
  expectResults "a generic function at a typed local" ["import lib;"] []
    "{ let h: function (word) returns (word) = lib.id; return h(a0); }" same
  expectResults "passed to a generic function" ["import lib;"] [twice] "twice(lib.f, a0)" same
  expectResults "a generic function passed to a generic function" ["import lib;"] [twice]
    "twice(lib.id, a0)" same
  expectResults "through a module alias" ["import relay;"] [apply] "apply(relay.L.add, a0)" [4, 4]
  expectResults "through a wildcard re-export" ["import lib4;"] [apply] "apply(lib4.add, a0)"
    [4, 4]
  expectResults "through a selected re-export" ["import lib3;"] [apply1] "apply1(lib3.f, a0)" same
  expectResults "through a module exported by its name" ["import lib5;"] [apply]
    "apply(lib5.lib.add, a0)" [4, 4]
  expectResults "a nested import's last component" ["import pkg.mod;"] [apply1]
    "apply1(mod.g, a0)" same
  expectResults "a conditional of two" ["import lib;"] [apply] "apply(true ? lib.add : lib.k, a0)"
    [4, 4]
  expectResults "returned by a function" ["import lib;"]
    ["function pick() returns (function (word, word) returns (word)) { return lib.add; }"]
    "{ let g = pick(); return g(a0, 4); }" [4, 4]
  expectResults "beside a local of its name" ["import lib;"]
    [apply, "function add(x: word, y: word) returns (word) { return x; }"]
    "apply(add, apply(lib.add, a0))" [4, 4]
  expectResults "unused" ["import lib;"] [] "{ let g = lib.add; return a0; }" same
  expectResults "a grouped callee" ["import lib;"] [] "(lib.add)(a0, 4)" [4, 4]
  expectResults "a re-exported std.opcodes function" ["import relaystd;"] [apply]
    "apply(relaystd.div, a0)" [2, maximum / 4]
  expectRefused "at the wrong type" ["import lib;"] []
    "{ let g: function (word) returns (word) = lib.add; return g(a0); }" "check"
  expectRefused "an unknown name" ["import lib;"] [apply] "apply(lib.nosuch, a0)" "check"
  expectRefused "a function the module does not export" ["import lib;"] [apply1]
    "apply1(lib.hidden, a0)" "check"
  expectRefused "a local named like the qualifier" ["import lib;"] [apply]
    "{ let lib: word = a0; return apply(lib.add, a0); }" "check"
  expectRefused "no import" [] [apply] "apply(lib.add, a0)" "check"
  expectRefused "a selected import" ["import { add } from lib;"] [apply] "apply(lib.add, a0)"
    "check"
  expectRefused "a type" ["import lib;"] [apply1] "apply1(lib.Color, a0)" "check"

/-- A nested plain import's full path, accepted with upstream's results beside its last component,
and the paths upstream refuses: the first component alone or as a value, the last two of three,
the path of a namespace import, `lib` before an absolute path, and a local of the first
component's name, which upstream's `SC0121` refuses beside a function too. -/
private def testFullPaths : IO Unit := do
  let same := [9, maximum]
  expectResults "a call" ["import pkg.mod;"] [] "pkg.mod.g(a0)" same
  expectResults "the last component" ["import pkg.mod;"] [] "mod.g(a0)" same
  expectResults "a value" ["import pkg.mod;"] [apply1] "apply1(pkg.mod.g, a0)" same
  expectResults "three components" ["import a.b.c;"] [] "a.b.c.g(a0)" same
  expectResults "three components, the last" ["import a.b.c;"] [] "c.g(a0)" same
  expectResults "two imports sharing a first component" ["import pkg.mod;", "import pkg.lt;"] []
    "pkg.lt.g(pkg.mod.g(a0))" [7, 7]
  expectResults "a type" ["import pkg.mod;"] [] "{ let s: pkg.mod.T = a0; return s; }" same
  expectResults "a type in a signature" ["import pkg.mod;"]
    ["function first(x: pkg.mod.T) returns (pkg.mod.T) { return x; }"] "first(a0)" same
  expectResults "a constructor" ["import pkg.mod;"] [] "pkg.mod.toWord(pkg.mod.Shape.Line)" [2, 2]
  expectResults "a constructor pattern" ["import pkg.mod;"] []
    ("{ match (pkg.mod.Shape.Line) { case pkg.mod.Shape.Dot { return 1; } " ++
      "case pkg.mod.Shape.Line { return 2; } } }") [2, 2]
  expectResults "a module alias under the full path" ["import pkg.relay;"] []
    "pkg.relay.L.add(a0, 4)" [4, 4]
  expectResults "a module alias under the last component" ["import pkg.relay;"] []
    "relay.L.add(a0, 4)" [4, 4]
  expectResults "an absolute lib path, the path it is seen by" ["import lib.pkg.mod;"] []
    "pkg.mod.g(a0)" same
  expectResults "a module beside its directory" ["import pkg;", "import pkg.mod;"] []
    "pkg.h(pkg.mod.g(a0))" [3, 3] pkgModule
  expectResults "a namespace alias named like the first component"
    ["import pkg.mod;", "import * as pkg from lib;"] [] "pkg.f(pkg.mod.g(a0))" same
  expectResults "beside a selected import of the module"
    ["import pkg.mod;", "import { g } from pkg.mod;"] [] "pkg.mod.g(g(a0))" same
  expectResults "a namespace import's alias" ["import * as M from pkg.mod;"] [] "M.g(a0)" same
  expectRefused "the first component alone" ["import pkg.mod;"] [] "pkg.g(a0)" "check"
  expectRefused "the first component as a value" ["import pkg.mod;"] [apply1] "apply1(pkg, a0)"
    "check"
  expectRefused "the last two of three" ["import a.b.c;"] [] "b.c.g(a0)" "check"
  expectRefused "a namespace import's path" ["import * as M from pkg.mod;"] [] "pkg.mod.g(a0)"
    "check"
  expectRefused "lib before an absolute path" ["import lib.pkg.mod;"] [] "lib.pkg.mod.g(a0)" "check"
  expectRefused "a local named like the first component" ["import pkg.mod;"] []
    "{ let pkg: word = a0; return pkg.mod.g(a0); }" "check"
  expectRefused "a function named like the first component" ["import pkg.mod;"]
    ["function pkg(x: word) returns (word) { return x; }"] "mod.g(a0)" "load"

def run : IO Unit := do
  testValues
  testFullPaths
  IO.println "qualified names of user modules: upstream's forms and results GREEN"

end Tests.QualifiedNames
