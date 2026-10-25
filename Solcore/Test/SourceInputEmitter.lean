import Solcore.Synthesis.Source.InputEmitter
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec.Program

/-! Runtime-input profile checks: admission, capture-avoiding abstraction,
independent Core application and source formatting. These are printer tests,
not a source-to-Core meaning-preservation theorem. -/
set_option autoImplicit false

namespace Tests.SourceInputEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (body : Wire.Expr) : IO CheckedWordFunction :=
  match CheckedWordFunction.ofBody? body with
  | some function => pure function
  | none => throw (IO.userError "runtime-input fixture failed its profile or Core check")

private def sourceProgram (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body} with
  | some program => pure program
  | none => throw (IO.userError "literal-abstraction fixture is not a checked G0 program")

private def emitted (function : CheckedWordFunction) : IO EmittedProgram :=
  match Input.emit function with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"runtime-input fixture emission failed: {reprStr error}")

private def observe (function : CheckedWordFunction) (input expected : Nat) : IO Unit := do
  let argument := Word.ofNatModulo input
  ensure ((function.instantiate argument).check) "applied input function failed Core typing"
  match (function.instantiate argument).toCore.runStateful 1000 with
  | .done (.word actual) _ => ensure (actual.val == expected) "runtime-input Core result changed"
  | _ => throw (IO.userError "runtime-input Core application did not return a Word")

private def sameExpr (left right : Wire.Expr) : Bool := Wire.encodeExpr left == Wire.encodeExpr right

/-- A Word input below an outer local and both branch-local binders. -/
def scopedInput : Wire.Expr :=
  .letE (word 7) (.ifE (.binary .wordGt (.var 1) (word 0))
    (.letE (word 11) (.binary .wordAdd (.var 1) (.var 2)))
    (.letE (word 22) (.binary .wordSub (.var 2) (.var 1))))

/-- Reusable scalar inputs for frontend integration tests. Every enabled
primitive occurs in a computation whose result can depend on runtime input. -/
def fixtures : List (String × Wire.Expr) := [
  ("identity", .var 0),
  ("word-not", .unary .wordNot (.var 0)),
  ("word-add", .binary .wordAdd (.var 0) (word 1)),
  ("word-sub", .binary .wordSub (.var 0) (word 1)),
  ("word-mul", .binary .wordMul (.var 0) (word 2)),
  ("word-and", .binary .wordAnd (.var 0) (word 10)),
  ("word-or", .binary .wordOr (.var 0) (word 10)),
  ("word-xor", .binary .wordXor (.var 0) (word 10)),
  ("word-eq", .ifE (.binary .wordEq (.var 0) (.word Word.maximum)) (word 1) (word 0)),
  ("word-gt", .ifE (.binary .wordGt (.var 0) (word (2 ^ 255 - 1))) (word 1) (word 0)),
  ("bool-not", .ifE (.unary .boolNot (.binary .wordEq (.var 0) (word 0))) (word 1) (word 0)),
  ("scoped-input", scopedInput)]

private def admissionChecks : IO Unit := do
  let identity ← checked (.var 0)
  ensure identity.program.check "admitted function was not checked"
  let some readBack := CheckedWordFunction.ofProgram? identity.program |
    throw (IO.userError "canonical function program failed readmission")
  ensure (sameExpr readBack.body identity.body) "function readmission changed its body"
  for body in [(.var 1 : Wire.Expr), .bool true,
      .letE (word 0) (.var 2), .lambda .word .word (.var 0),
      .apply (.lambda .word .word (.var 0)) (word 0)] do
    ensure (CheckedWordFunction.ofBody? body).isNone
      "function profile admitted a host variable, wrong type or nested function"
  for program in [
      ({resultType := .word, dataDefinitions := [], body := word 0} : Wire.Program),
      {identity.program with resultType := .function .bool .word},
      {identity.program with body := .lambda .word .bool (.bool false)},
      {identity.program with dataDefinitions := [{constructorPayloadTypes := []}]}] do
    ensure (CheckedWordFunction.ofProgram? program).isNone
      "function profile admitted a different program shape"
  for input in [0, 1, Word.maximum.val, 2 ^ 255] do observe identity input input
  match (identity.instantiate Word.zero).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero-fuel function application was treated as completed")

private def abstractionChecks : IO Unit := do
  let original : Wire.Expr := .letE (word 7)
    (.letE (word 11) (.binary .wordAdd (.var 1) (word 22)))
  ensure ((wordLiterals original).map (fun value => value.val) == [7, 11, 22] && literalCount original == 3)
    "Word literal preorder changed"
  let expected : List Wire.Expr := [
    .letE (.var 0) (.letE (word 11) (.binary .wordAdd (.var 1) (word 22))),
    .letE (word 7) (.letE (.var 1) (.binary .wordAdd (.var 1) (word 22))),
    .letE (word 7) (.letE (word 11) (.binary .wordAdd (.var 1) (.var 2)))]
  let source ← sourceProgram original
  for (index, body) in expected.zipIdx |>.map (fun (body, index) => (index, body)) do
    let some actual := abstractWordLiteral original index |
      throw (IO.userError "in-range Word literal abstraction was rejected")
    ensure (sameExpr actual body) "Word literal abstraction captured or shifted an existing local"
    let some function := CheckedWordFunction.fromProgram? source index |
      throw (IO.userError "abstracted function failed checked admission")
    ensure (sameExpr function.body body) "checked abstraction changed the candidate"
    let _ ← emitted function
    observe function 5 (if index == 0 then 27 else if index == 1 then 29 else 12)
  for index in [3, 4, 100] do
    ensure ((abstractWordLiteral original index).isNone &&
      (CheckedWordFunction.fromProgram? source index).isNone)
      "out-of-range literal selection was silently replaced"
  let initializer : Wire.Expr := .letE (word 7)
    (.letE (.binary .wordAdd (.var 0) (word 11)) (.binary .wordSub (.var 0) (.var 1)))
  let some changed := CheckedWordFunction.fromProgram? (← sourceProgram initializer) 1 |
    throw (IO.userError "initializer abstraction failed")
  observe changed 5 5
  let branches : Wire.Expr := .ifE (.bool true) (word 1) (.letE (word 2) (word 3))
  ensure ((wordLiterals branches).map (fun value => value.val) == [1, 2, 3]) "literal traversal skipped an untaken branch"
  let some last := abstractWordLiteral branches 2 | throw (IO.userError "untaken literal was not selectable")
  ensure (sameExpr last (.ifE (.bool true) (word 1) (.letE (word 2) (.var 1))))
    "untaken branch literal acquired the wrong parameter index"

private def executionChecks : IO Unit := do
  for (label, body) in fixtures do
    let function ← checked body
    let first ← emitted function
    ensure (first == (← emitted function)) s!"input emission is not deterministic: {label}"
    ensure (first.contractName == "SynthesizedInput" && first.methodName == "run" &&
      first.methodSignature == "run(uint256)" && first.deployPath == ["SynthesizedInputDeploy"] &&
      first.runtimePath == ["SynthesizedInputDeploy", "SynthesizedInput"])
      s!"input wrapper metadata changed: {label}"
  for (label, input, expected) in [
      ("word-not", 0, Word.maximum.val), ("word-not", Word.maximum.val, 0),
      ("word-add", Word.maximum.val, 0), ("word-sub", 0, Word.maximum.val),
      ("word-mul", 2 ^ 255, 0), ("word-and", 252, 8),
      ("word-or", 252, 254), ("word-xor", 252, 246),
      ("word-eq", Word.maximum.val, 1), ("word-eq", 0, 0),
      ("word-gt", 2 ^ 255, 1), ("word-gt", 1, 0),
      ("bool-not", 0, 0), ("bool-not", 1, 1),
      ("scoped-input", 0, Word.maximum.val - 6), ("scoped-input", 1, 8)] do
    let some (_, body) := fixtures.find? (fun entry => entry.1 == label) |
      throw (IO.userError s!"missing runtime-input fixture {label}")
    observe (← checked body) input expected
  for (body, expected) in [
      (.unary .wordClz (.var 0), EmitError.unsupportedUnary .wordClz),
      (.binary .wordDiv (.var 0) (word 0), .unsupportedBinary .wordDiv),
      (.ternary .wordAddMod (.var 0) (word 1) (word 2), .unsupportedTernary .wordAddMod)] do
    match Input.emit (← checked body) with
    | .error actual => ensure (actual == expected) "unsupported input operation returned the wrong error"
    | .ok _ => throw (IO.userError "unsupported input operation was silently emitted")

private def formattingChecks : IO Unit := do
  let identityExpected := String.intercalate "\n" [
    "import * from std;", "import * from std.dispatch;", "",
    "contract SynthesizedInput {",
    "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        return uint256(sc_input);", "    }", "}", ""]
  ensure ((← emitted (← checked (.var 0))).source == identityExpected)
    "input emission no longer reads the runtime ABI parameter"
  let bindingExpected := String.intercalate "\n" [
    "import * from std;", "import * from std.dispatch;", "",
    "contract SynthesizedInput {",
    "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_v0: word = 7;", "        let sc_v1: word = sc_v0;",
    "        let sc_v2: word = (sc_v1 + sc_input);",
    "        return uint256(sc_v2);", "    }", "}", ""]
  ensure ((← emitted (← checked (.letE (word 7) (.binary .wordAdd (.var 0) (.var 1))))).source == bindingExpected)
    "local binding hid or renamed the runtime input"
  ensure (Input.emitterVersion == "solcore-source-input-v1" &&
    Input.wrapperVersion == "solcore-word-input-contract-v1" && Input.selector == "0xa444f5e9" &&
    wordFunctionVersion == "core-word-function-v1" && abstractionVersion == "word-literal-preorder-v1")
    "input-profile provenance changed"

def testSourceInputEmitter : IO Unit := do
  admissionChecks
  abstractionChecks
  executionChecks
  formattingChecks

end Tests.SourceInputEmitter
