import Solcore.Frontend.SourceCompiler

/-!
# `std.opcodes` imports

Upstream's `std.opcodes` as a module of the load: its 81 functions bound by selected, aliased,
wildcard and hiding imports, the 26 pure ones as builtins, the other 55 refused where they are
used. Each case is a source upstream's pinned checker was probed with, and gives upstream's
verdict; an accepted one runs at 9 and 2^256 − 1 and gives the results upstream's checked Hull
gives. std's other modules bind no name, so a name resolves past their imports, and a name they
export is refused where it is used (`testBesideStandardModules`). A plain import's last component
and full path, and a namespace import's alias, qualify the module's functions (`testQualified`).
Operators beside a bound name follow upstream's three kinds (`testOperators`).
-/

set_option autoImplicit false

namespace Tests.StdOpcodes

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def maximum : Nat := 2 ^ 256 - 1

private def library : String := String.intercalate "\n" [
  "pragma solcore;",
  "export { add, f };",
  "function add(x: word, y: word) returns (word) { return y; }",
  "function f(x: word) returns (word) { return x; }"]

private def workspace (imports declarations : List String) (body : String) :
    Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    { path := "main.solc", content := String.intercalate "\n" (["pragma solcore;"] ++ imports ++
        declarations ++ [s!"function main(a0: word) returns (word) \{ return {body}; }"]) },
    { path := "lib.solc", content := library }]
  externalLibraries := []
}

/-- The function `main` loaded, checked, compiled and run at each input, or the stage that
refused it. -/
private def runMain (raw : Workspace.RawWorkspace) (inputs : List Nat) : IO (Except String (List Nat)) := do
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
    (expected : List Nat) : IO Unit := do
  let found ← runMain (workspace imports declarations body) [9, maximum]
  assertTrue (match found with | .ok results => results == expected | .error _ => false)
    s!"{label}: expected {expected}, got {reprStr found}"

private def expectRefused (label : String) (imports declarations : List String) (body : String)
    (stage : String) : IO Unit := do
  let found ← runMain (workspace imports declarations body) [9]
  assertTrue (match found with | .error refused => refused == stage | .ok _ => false)
    s!"{label}: expected a refusal at {stage}, got {reprStr found}"

private def localDiv : String := "function div(x: word, y: word) returns (word) { return x; }"

private def apply : String :=
  "function apply(g: function (word, word) returns (word), x: word) returns (word) { return g(x, 4); }"

/-- Forms upstream accepts, with its results at 9 and 2^256 − 1. -/
private def testAccepted : IO Unit := do
  let quarter := [2, maximum / 4]
  expectResults "selected" ["import { div } from std.opcodes;"] [] "div(a0, 4)" quarter
  expectResults "aliased" ["import { div as sc_div } from std.opcodes;"] [] "sc_div(a0, 4)" quarter
  expectResults "wildcard" ["import * from std.opcodes;"] [] "div(a0, 4)" quarter
  expectResults "wildcard hiding one, another used" ["import * from std.opcodes hiding { div };"] []
    "mod(a0, 4)" [1, 3]
  expectResults "wildcard hiding one, a local of it" ["import * from std.opcodes hiding { div };"]
    [localDiv] "div(a0, 4)" [9, maximum]
  expectResults "an alias, a local of the original name"
    ["import { div as sc_div } from std.opcodes;"] [localDiv] "sc_div(div(a0, 4), 2)"
    [4, maximum / 2]
  expectResults "an effectful function imported, unused" ["import { mload } from std.opcodes;"] []
    "a0" [9, maximum]
  expectResults "a wildcard, nothing used" ["import * from std.opcodes;"] [] "a0" [9, maximum]
  expectResults "the same item in two imports"
    ["import { div } from std.opcodes;", "import { div } from std.opcodes;"] [] "div(a0, 4)" quarter
  expectResults "one alias in two imports, the first kept"
    ["import { div as h } from std.opcodes;", "import { mod as h } from std.opcodes;"] []
    "h(a0, 4)" quarter
  expectResults "a wildcard, then an alias of another function"
    ["import * from std.opcodes;", "import { mod as div } from std.opcodes;"] [] "div(a0, 4)" quarter
  expectResults "an effectful and a pure function, the pure used"
    ["import { mload, div } from std.opcodes;"] [] "div(a0, 4)" quarter
  expectResults "an aliased opcode as a function value"
    ["import { div as sc_div } from std.opcodes;"] [apply] "apply(sc_div, a0)" quarter
  expectResults "a wildcard opcode as a function value" ["import * from std.opcodes;"] [apply]
    "apply(shr, a0)" [0, 0]

/-- Forms upstream refuses, refused at the load or where the name is used. -/
private def testRefused : IO Unit := do
  expectRefused "an alias, the original used" ["import { div as sc_div } from std.opcodes;"] []
    "div(a0, 4)" "check"
  expectRefused "a wildcard hiding one, it used" ["import * from std.opcodes hiding { div };"] []
    "div(a0, 4)" "check"
  expectRefused "a wildcard and a local of an export" ["import * from std.opcodes;"] [localDiv]
    "div(a0, 4)" "load"
  expectRefused "a wildcard and a local named like an effectful export"
    ["import * from std.opcodes;"] ["function mload(x: word) returns (word) { return x; }"] "a0"
    "load"
  expectRefused "a selected function and a local of its name" ["import { div } from std.opcodes;"]
    [localDiv] "div(a0, 4)" "load"
  expectRefused "an unknown item" ["import { nosuch } from std.opcodes;"] [] "a0" "load"
  expectRefused "an unknown hidden item" ["import * from std.opcodes hiding { nosuch };"] [] "a0"
    "load"
  expectRefused "an effectful function used" ["import { mload } from std.opcodes;"] [] "mload(a0)"
    "check"
  expectRefused "one item twice" ["import { div, div } from std.opcodes;"] [] "div(a0, 4)" "load"
  expectRefused "one item and its alias" ["import { div, div as d } from std.opcodes;"] []
    "d(div(a0, 4), 2)" "load"
  expectRefused "one alias twice" ["import { div as h, mod as h } from std.opcodes;"] []
    "h(a0, 4)" "load"
  expectRefused "one name from std.opcodes and a user module"
    ["import { add } from std.opcodes;", "import { add } from lib;"] [] "a0" "load"
  expectRefused "the same, used" ["import { add } from std.opcodes;", "import { add } from lib;"] []
    "add(a0, 4)" "load"
  expectRefused "two wildcards sharing a name" ["import * from std.opcodes;", "import * from lib;"] []
    "a0" "load"
  expectRefused "a plain import and a local of its qualifier" ["import std.opcodes;"]
    ["function opcodes(x: word) returns (word) { return x; }"] "opcodes(a0)" "load"
  expectRefused "a plain import, a bare call" ["import std.opcodes;"] [] "div(a0, 4)" "check"
  expectRefused "no import, a qualified call" [] [] "std.opcodes.div(a0, 4)" "check"
  expectRefused "std and std.opcodes wildcards, nothing used"
    ["import * from std;", "import * from std.opcodes;"] [] "a0" "load"

/-- Operators beside the names an import of `std.opcodes` binds, as upstream gives them. `<` and
`!` call the `lt` and `not` in scope, `<` with a bool expected, so a bound `lt` refuses `<` in a
condition, and `!` is the bound `not`: refused on a bool, upstream's results on a word. Trait
methods (`>>`, `%`) and the builtins `&&` and `||` see no bound name and keep Lean's builtins,
where upstream needs std's traits. -/
private def testOperators : IO Unit := do
  expectRefused "< beside a selected lt" ["import { lt } from std.opcodes;"] []
    "(a0 < 10) ? 1 : 0" "check"
  expectRefused "< beside a wildcard" ["import * from std.opcodes;"] [] "(a0 < 10) ? 1 : 0" "check"
  expectRefused "! in a condition beside a selected not" ["import { not } from std.opcodes;"] []
    "(!(a0 == 9)) ? 1 : 0" "check"
  expectResults "! on a word beside a selected not" ["import { not } from std.opcodes;"] [] "!a0"
    [maximum - 9, 0]
  expectResults "!! on a word" ["import { not } from std.opcodes;"] [] "!!a0" [9, maximum]
  expectResults "! on a word as an argument" ["import * from std.opcodes;"] [] "add(!a0, 1)"
    [maximum - 8, 1]
  expectResults ">> beside a selected shr" ["import { shr } from std.opcodes;"] [] "a0 >> 2"
    [2, maximum / 4]
  expectResults "% beside a selected mod" ["import { mod } from std.opcodes;"] [] "a0 % 4" [1, 3]
  expectResults "&& and || beside selected and and or" ["import { and, or } from std.opcodes;"] []
    "((true && true) || false) ? 1 : 0" [1, 1]

/-- Names past an import of std's other modules, which bind none: a function of `std.opcodes`,
Lean's operators and the twelve types' conversions, at upstream's results. A function std exports
is refused where it is used, as Lean has none of std's declarations. -/
private def testBesideStandardModules : IO Unit := do
  let quarter := [2, maximum / 4]
  expectResults "a std wildcard, a std.opcodes function used"
    ["import * from std;", "import { div } from std.opcodes;"] [] "div(a0, 4)" quarter
  expectResults "a std.dispatch wildcard, a std.opcodes function used"
    ["import * from std.dispatch;", "import { div } from std.opcodes;"] [] "div(a0, 4)" quarter
  expectResults "std, std.opcodes hiding the ten it shares"
    ["import * from std;",
      "import * from std.opcodes hiding { addmod, address, and, byte, gt, " ++
        "log1, lt, mulmod, not, or };"]
    [] "div(a0, 4)" quarter
  expectResults "std hiding not, not from std.opcodes"
    ["import * from std hiding { not };", "import { not } from std.opcodes;"] [] "not(a0)"
    [maximum - 9, 0]
  expectResults "< beside std" ["import * from std;"] [] "(a0 < 10) ? 1 : 0" [1, 0]
  expectResults "<< beside std" ["import * from std;"] [] "a0 << 2" [36, maximum - 3]
  expectResults "! beside std" ["import * from std;"] [] "(!false) ? 1 : 0" [1, 1]
  expectResults "uint256 and Typedef.rep beside std" ["import * from std;"] []
    "Typedef.rep(uint256(a0))" [9, maximum]
  expectRefused "a function std exports, used" ["import * from std;"] [] "tobool(a0) ? 1 : 0"
    "check"

/-- Qualified access, as upstream gives it: `opcodes` and `std.opcodes` after a plain import, and a
namespace import's alias, qualify the 26 pure functions in calls and as values. An effectful
function under them is refused where it is used, as after the other imports, and so are an unknown
name, a wrong arity, and a qualifier no import of `std.opcodes` gives. -/
private def testQualified : IO Unit := do
  let quarter := [2, maximum / 4]
  expectResults "a plain import, a qualified call" ["import std.opcodes;"] [] "opcodes.div(a0, 4)"
    quarter
  expectResults "a plain import, a fully qualified call" ["import std.opcodes;"] []
    "std.opcodes.div(a0, 4)" quarter
  expectResults "a qualified opcode as a function value" ["import std.opcodes;"] [apply]
    "apply(opcodes.sub, a0)" [5, maximum - 4]
  expectResults "a fully qualified opcode as a function value" ["import std.opcodes;"] [apply]
    "apply(std.opcodes.sub, a0)" [5, maximum - 4]
  expectResults "a namespace import's alias" ["import * as O from std.opcodes;"] [] "O.div(a0, 4)"
    quarter
  expectResults "nested qualified calls" ["import std.opcodes;"] []
    "opcodes.div(opcodes.add(a0, 3), 4)" [3, 0]
  expectResults "plain and selected imports, both used"
    ["import std.opcodes;", "import { div } from std.opcodes;"] [] "opcodes.div(div(a0, 2), 2)"
    quarter
  expectResults "a plain import and a local div, both used" ["import std.opcodes;"] [localDiv]
    "opcodes.div(div(a0, 4), 2)" [4, maximum / 2]
  expectResults "a qualified ternary" ["import std.opcodes;"] [] "opcodes.addmod(a0, 1, 5)" [0, 1]
  expectResults "a qualified comparison" ["import std.opcodes;"] [] "opcodes.lt(a0, 10)" [1, 0]
  expectResults "plain imports of std.opcodes and lib" ["import std.opcodes;", "import lib;"] []
    "lib.f(opcodes.div(a0, 4))" quarter
  expectRefused "an effectful function, qualified" ["import std.opcodes;"] [] "opcodes.mload(a0)"
    "check"
  expectRefused "an effectful function under an alias" ["import * as O from std.opcodes;"] []
    "O.mload(a0)" "check"
  expectRefused "an unknown name, qualified" ["import std.opcodes;"] [] "opcodes.nosuch(a0)" "check"
  expectRefused "a wrong arity, qualified" ["import std.opcodes;"] [] "opcodes.div(a0)" "check"
  expectRefused "a plain import of std, std.opcodes qualified" ["import std;"] []
    "std.opcodes.div(a0, 4)" "check"
  expectRefused "no import, a qualified call" [] [] "opcodes.div(a0, 4)" "check"

def run : IO Unit := do
  testAccepted
  testRefused
  testBesideStandardModules
  testQualified
  testOperators
  IO.println "std.opcodes and std imports, operators: upstream's forms and results GREEN"

end Tests.StdOpcodes
