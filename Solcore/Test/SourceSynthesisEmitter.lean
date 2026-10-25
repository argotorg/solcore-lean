import Solcore.Synthesis.Source.Emitter

/-! Source-emission regressions for the supported scalar subset. These tests
check representation and scope; Rust acceptance and differential execution
are separate checks, not consequences of these string assertions. -/
set_option autoImplicit false
namespace Tests.SourceSynthesisEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

/-- A shared fixture carrier for the case runner and external Rust checks. -/
def fixtureProgram (body : Wire.Expr) : Wire.Program :=
  {resultType := .word, dataDefinitions := [], body}

private def comparison (operation : Wire.BinaryOp) (left right : Wire.Expr) : Wire.Expr :=
  .ifE (.binary operation left right) (word 1) (word 0)

/-- The true arm reads the outer binder; the false arm reads its own binder.
The final addition must still see the outer binder after either branch. -/
def scopedBranch (selected : Bool) : Wire.Expr :=
  .letE (word 7) (.binary .wordAdd
    (.ifE (.bool selected) (.letE (word 11) (.var 1)) (.letE (word 22) (.var 0))) (.var 0))

/-- Every initially supported primitive has a fixture, including modular and
unsigned boundaries. All fixtures pass the original G0 checker. -/
def fixtures : List (String × Wire.Expr) := [
  ("zero", word 0),
  ("maximum", .word Word.maximum),
  ("add-wrap", .binary .wordAdd (.word Word.maximum) (word 1)),
  ("sub-wrap", .binary .wordSub (word 0) (word 1)),
  ("mul-wrap", .binary .wordMul (word (2 ^ 255)) (word 2)),
  ("word-and", .binary .wordAnd (word 252) (word 10)),
  ("word-or", .binary .wordOr (word 252) (word 10)),
  ("word-xor", .binary .wordXor (word 252) (word 10)),
  ("word-not", .unary .wordNot (word 10)),
  ("word-equal", comparison .wordEq (.word Word.maximum) (.word Word.maximum)),
  ("word-greater-unsigned", comparison .wordGt (word (2 ^ 255)) (word 1)),
  ("bool-not", .ifE (.unary .boolNot (.bool false)) (word 55) (word 99)),
  ("nested-locals", .letE (word 7) (.letE (word 9) (.binary .wordSub (.var 1) (.var 0)))),
  ("branch-scope-true", scopedBranch true),
  ("branch-scope-false", scopedBranch false)]

private def unsupportedBinaries : List Wire.BinaryOp :=
  [.wordDiv, .wordMod, .wordSgt, .wordShl, .wordShr, .wordByte, .wordSar,
    .wordPow, .wordSignExtend, .wordSdiv, .wordSmod]

private def binaryWordBody (operation : Wire.BinaryOp) : Wire.Expr :=
  if operation == .wordSgt then comparison operation (word 2) (word 1)
  else .binary operation (word 2) (word 1)

private def unsupportedFixtures : List (Wire.Expr × EmitError) :=
  [(.unary .wordClz (word 1), .unsupportedUnary .wordClz)] ++
  unsupportedBinaries.map (fun operation => (binaryWordBody operation, .unsupportedBinary operation)) ++
  [(.ternary .wordAddMod (word 1) (word 2) (word 3), .unsupportedTernary .wordAddMod),
   (.ternary .wordMulMod (word 1) (word 2) (word 3), .unsupportedTernary .wordMulMod),
   (.ifE (.bool true) (word 1) (.binary .wordDiv (word 1) (word 0)), .unsupportedBinary .wordDiv)]

private def admit (body : Wire.Expr) : IO CheckedWordProgram := do
  match CheckedWordProgram.ofProgram? (fixtureProgram body) with
  | some checked => pure checked
  | none => throw (IO.userError "emitter fixture failed the original G0 checker")

private def emitted (body : Wire.Expr) : IO EmittedProgram := do
  match emit (← admit body) with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"supported emitter fixture was rejected: {reprStr error}")

private def scopedExpected : String := String.intercalate "\n" [
  "import * from std;",
  "import * from std.dispatch;",
  "",
  "contract SynthesizedG0 {",
  "    function run() public returns (uint256) {",
  "        let sc_v0: word = 7;",
  "        let sc_v1: word = sc_v0;",
  "        let sc_v2: bool = false;",
  "        let sc_v3: word = 0;",
  "        if (sc_v2) {",
  "            let sc_v4: word = 11;",
  "            let sc_v5: word = sc_v4;",
  "            sc_v3 = sc_v1;",
  "        } else {",
  "            let sc_v6: word = 22;",
  "            let sc_v7: word = sc_v6;",
  "            sc_v3 = sc_v7;",
  "        }",
  "        let sc_v8: word = (sc_v3 + sc_v1);",
  "        return uint256(sc_v8);",
  "    }",
  "}", ""]

private def nestedExpected : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;", "",
  "contract SynthesizedG0 {", "    function run() public returns (uint256) {",
  "        let sc_v0: word = 7;", "        let sc_v1: word = sc_v0;",
  "        let sc_v2: word = 9;", "        let sc_v3: word = sc_v2;",
  "        let sc_v4: word = (sc_v1 - sc_v3);", "        return uint256(sc_v4);",
  "    }", "}", ""]

def testSourceSynthesisEmitter : IO Unit := do
  for (label, body) in fixtures do
    unless supported body do
      throw (IO.userError s!"supported source fixture misclassified: {label}")
    let result ← emitted body
    unless result.contractName == contractName && result.methodName == methodName &&
        result.methodSignature == "run()" && result.deployPath == ["SynthesizedG0Deploy"] &&
        result.runtimePath == ["SynthesizedG0Deploy", "SynthesizedG0"] do
      throw (IO.userError s!"source wrapper metadata changed: {label}")
    unless result == (← emitted body) do
      throw (IO.userError s!"source emission is not deterministic: {label}")
  for (body, expected) in unsupportedFixtures do
    unless !supported body do
      throw (IO.userError "unsupported source fixture was marked supported")
    match emit (← admit body) with
    | .error actual =>
      unless actual == expected do
        throw (IO.userError s!"unsupported source operation returned the wrong error: {reprStr actual}")
    | .ok _ =>
      throw (IO.userError s!"unsupported source operation was not rejected explicitly: {reprStr expected}")
  unless (← emitted (scopedBranch false)).source == scopedExpected do
    throw (IO.userError "branch-local emission changed its scope, ordering or binding indices")
  unless (← emitted (.letE (word 7) (.letE (word 9) (.binary .wordSub (.var 1) (.var 0))))).source == nestedExpected do
    throw (IO.userError "nested Core bindings changed during source emission")
  let maximum ← emitted (.word Word.maximum)
  unless (maximum.source.splitOn (toString Word.maximum.val)).length == 2 do
    throw (IO.userError "source emission truncated a 256-bit Word literal")
  unless emitterVersion == "solcore-source-g0-v1" && wrapperVersion == "solcore-word-contract-v1" do
    throw (IO.userError "emitter provenance version changed")

end Tests.SourceSynthesisEmitter
