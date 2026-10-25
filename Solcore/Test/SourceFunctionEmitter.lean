import Solcore.Synthesis.Source.FunctionEmitter
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec.Program

/-! Named-function source regressions. The original Core graphs independently
exercise ordered declarations, diamond dependencies and calls under local
binders. Printer tests do not establish compiler meaning preservation. -/
set_option autoImplicit false

namespace Tests.SourceFunctionEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

def entry : Wire.Expr := .apply (.var 1) (.var 0)

def singleHelpers : List Wire.Expr := [.binary .wordAdd (.var 0) (word 1)]

def chainHelpers : List Wire.Expr := singleHelpers ++ [
  .binary .wordMul (.var 0) (.apply (.var 1) (.var 0))]

/-- The last helper calls both earlier helpers. Its inner binder shifts the
callee index, while the parameter must remain distinct from the new local. -/
def diamondHelpers : List Wire.Expr := singleHelpers ++ [
  .binary .wordAdd (.var 0) (.apply (.var 1) (.var 0)),
  .letE (.apply (.var 2) (.var 0))
    (.binary .wordSub (.apply (.var 2) (.var 1)) (.var 0))]

def scopedHelpers : List Wire.Expr := singleHelpers ++ [
  .letE (word 7) (.ifE (.binary .wordGt (.var 1) (word 0))
    (.letE (word 11) (.apply (.var 3) (.binary .wordAdd (.var 0) (.var 2))))
    (.letE (word 22) (.apply (.var 3) (.binary .wordSub (.var 2) (.var 1)))))]

def fixtures : List (String × List Wire.Expr × Wire.Expr) := [
  ("single", singleHelpers, entry), ("chain", chainHelpers, entry),
  ("diamond", diamondHelpers, entry), ("branch-locals", scopedHelpers, entry)]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedWordFunctionDAG :=
  match CheckedWordFunctionDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "function graph fixture failed checked profile admission")

private def emitted (graph : CheckedWordFunctionDAG) : IO EmittedProgram :=
  match Function.emit graph with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"function graph emission failed: {reprStr error}")

private def observe (graph : CheckedWordFunctionDAG) (input expected : Nat) : IO Unit := do
  let applied := graph.instantiate (Word.ofNatModulo input)
  ensure applied.check "original applied function graph failed Core typing"
  match applied.toCore.runStateful 2000 with
  | .done (.word actual) _ => ensure (actual.val == expected) "original Core function graph result changed"
  | _ => throw (IO.userError "original Core function graph did not return a Word")

private def admissionChecks : IO Unit := do
  for (label, helpers, body) in fixtures do
    let graph ← checked helpers body
    ensure (graph.program.check && functionHelpersAccepted helpers &&
      functionAcceptsAt 1 helpers.length .word body) s!"graph was not fully admitted: {label}"
    let some restored := CheckedWordFunctionDAG.ofProgram? graph.program |
      throw (IO.userError s!"canonical graph failed readmission: {label}")
    ensure (Wire.encodeProgram restored.program == Wire.encodeProgram graph.program)
      s!"graph readmission reordered declarations: {label}"
    let source ← emitted graph
    ensure (source == (← emitted graph)) s!"graph emission was not deterministic: {label}"
    ensure (source.contractName == "SynthesizedFunctions" && source.methodSignature == "run(uint256)" &&
      source.deployPath == ["SynthesizedFunctionsDeploy"] &&
      source.runtimePath == ["SynthesizedFunctionsDeploy", "SynthesizedFunctions"])
      s!"graph wrapper metadata changed: {label}"
  ensure (CheckedWordFunctionDAG.ofParts? [] (.var 0)).isNone "empty helper graph was admitted"
  ensure (CheckedWordFunctionDAG.ofParts? (List.replicate 4 (.var 0)) entry).isNone
    "helper count exceeded the fixed profile bound"
  for helpers in [
      [(.apply (.var 1) (.var 0) : Wire.Expr)],
      singleHelpers ++ [.apply (.var 2) (.var 0)],
      [(.var 1 : Wire.Expr)],
      [(.apply (.var 0) (.var 0) : Wire.Expr)],
      [(.letE (.lambda .word .word (.var 0)) (.apply (.var 0) (word 1)) : Wire.Expr)]] do
    ensure (CheckedWordFunctionDAG.ofParts? helpers entry).isNone
      "graph admitted a recursive/forward/escaping/local function or host reference"
  -- The Core host context really contains Word-to-Word functions. The scalar
  -- profile, not a coincidental type error, must reject these out-of-graph calls.
  let hostRead := functionDAGProgram [.apply (.var 1) (.var 0)] entry
  ensure hostRead.check "host-reference boundary fixture stopped exercising a well-typed Core program"
  ensure (CheckedWordFunctionDAG.ofProgram? hostRead).isNone
    "full Core typing bypassed the graph's closed scope boundary"
  for body in [
      (.apply (.var 2) (.var 0) : Wire.Expr),
      .apply (.ifE (.bool true) (.var 1) (.var 1)) (.var 0),
      .var 1, .bool false, .lambda .word .word (.var 0)] do
    ensure (CheckedWordFunctionDAG.ofParts? singleHelpers body).isNone
      "graph entry admitted an out-of-profile function expression"
  let single ← checked singleHelpers
  for program in [
      {single.program with dataDefinitions := [{constructorPayloadTypes := []}]},
      {single.program with resultType := .word},
      {single.program with body := .lambda .word .word (.var 0)},
      {single.program with body := .letE (word 1) (.lambda .word .word (.var 0))}] do
    ensure (CheckedWordFunctionDAG.ofProgram? program).isNone
      "graph decoder accepted a different declaration shape"

private def executionChecks : IO Unit := do
  let single ← checked singleHelpers
  let chain ← checked chainHelpers
  let diamond ← checked diamondHelpers
  let withLocals ← checked scopedHelpers
  for input in [0, 1, Word.maximum.val, 2 ^ 255] do
    observe single input ((Word.ofNatModulo (input + 1)).val)
    observe diamond input input
  for (input, result) in [(0, 0), (1, 2), (Word.maximum.val, 0), (2 ^ 255, 2 ^ 255)] do
    observe chain input result
  for (input, result) in [(0, Word.maximum.val - 5), (1, 13),
      (Word.maximum.val, 11), (2 ^ 255, 2 ^ 255 + 12)] do
    observe withLocals input result
  match (chain.instantiate Word.zero).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero-fuel graph execution was treated as complete")
  for (body, expected) in [
      (.unary .wordClz (.var 0), EmitError.unsupportedUnary .wordClz),
      (.binary .wordDiv (.var 0) (word 0), .unsupportedBinary .wordDiv),
      (.ternary .wordMulMod (.var 0) (word 1) (word 2), .unsupportedTernary .wordMulMod)] do
    -- Even an unused helper must not be silently dropped by source emission.
    match Function.emit (← checked [body] (word 0)) with
    | .error actual => ensure (actual == expected) "unsupported graph operation returned the wrong error"
    | .ok _ => throw (IO.userError "unsupported graph operation was silently emitted")

private def chainExpected : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_fn1(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);",
  "    let sc_v1: word = (sc_arg * sc_v0);", "    return sc_v1;", "}", "",
  "contract SynthesizedFunctions {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_v0: word = sc_fn1(sc_input);",
  "        return uint256(sc_v0);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  ensure ((← emitted (← checked chainHelpers)).source == chainExpected)
    "helper declaration order, runtime parameter or direct-call rendering changed"
  let diamond ← checked diamondHelpers
  let source ← emitted diamond
  let third := String.intercalate "\n" [
    "function sc_fn2(sc_arg: word) returns (word) {",
    "    let sc_v0: word = sc_fn0(sc_arg);", "    let sc_v1: word = sc_v0;",
    "    let sc_v2: word = sc_fn1(sc_arg);", "    let sc_v3: word = (sc_v2 - sc_v1);",
    "    return sc_v3;", "}"]
  ensure ((source.source.splitOn third).length == 2)
    "inner local shifted a helper reference to the wrong declaration"
  let scopedSource ← emitted (← checked scopedHelpers)
  let beforeCall := String.intercalate "\n" [
    "        let sc_v7: word = (sc_v6 + sc_arg);",
    "        let sc_v8: word = sc_fn0(sc_v7);"]
  ensure ((scopedSource.source.splitOn beforeCall).length == 2)
    "branch-local argument computation escaped its block or moved after its call"
  let single ← checked singleHelpers
  ensure (single.features == ["binary:Solcore.Core.Wire.BinaryOp.wordAdd", "local", "wordLiteral",
    "functionCall", "local"]) "function features counted declaration wrappers or callee locals"
  ensure ((diamond.features.filter (· == "functionCall")).length == 4)
    "diamond feature inventory lost a helper dependency"
  ensure (Function.emitterVersion == "solcore-source-functions-v1" &&
    Function.wrapperVersion == "solcore-word-functions-contract-v1" &&
    Function.selector == "0xa444f5e9" && wordFunctionDAGVersion == "core-word-function-dag-v1")
    "named-function provenance changed"

def testSourceFunctionEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceFunctionEmitter
