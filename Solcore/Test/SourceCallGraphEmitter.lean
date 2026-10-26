import Solcore.Synthesis.Source.CallGraphEmitter
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec.Program

/-! Checked original Core goldens and source ordering regressions for arbitrary
acyclic scalar helper calls. These tests neither execute emitted source nor
prove compiler meaning preservation. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphEmitter
open Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def maximum : Nat := Word.maximum.val
private def high : Nat := 2 ^ 255

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (entry : Wire.Expr) : IO CheckedWordFunctionDAG :=
  match CheckedWordFunctionDAG.ofParts? helpers entry with
  | some graph => pure graph
  | none => throw (IO.userError "call graph failed checked admission")

private def emitted (graph : CheckedWordFunctionDAG) : IO EmittedProgram :=
  match CallGraph.emit graph with
  | .ok source => pure source
  | .error error => throw (IO.userError s!"call graph emission failed: {reprStr error}")

private def render (functions : List String) (target : Target) (locals : List String)
    (indent nextId : Nat) (body : Wire.Expr) : IO ScalarRenderer.Rendered :=
  match CallGraphRenderer.renderWithFunctions functions target locals indent nextId body with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"call graph rendering failed: {reprStr error}")

private def observe (graph : CheckedWordFunctionDAG) (input expected : Nat) : IO Unit := do
  let original := graph.instantiate (Word.ofNatModulo input)
  ensure original.check "original applied call graph failed Core typing"
  match original.toCore.runStateful 10000 with
  | .done (.word value) state =>
      ensure (value.val == expected) s!"original Core result {value.val} differs from {expected}"
      ensure state.isEmpty "scalar helper calls allocated a cell"
  | _ => throw (IO.userError "original Core call graph did not complete")

/-- Calls occur inside let initializers, branch predicates, primitive operands
and nested call arguments. The entry combines two different dependency paths. -/
def mixedHelpers : List Wire.Expr := [
  .binary .wordAdd (.var 0) (word 1),
  .letE (call 1 (.var 0))
    (.ifE (.binary .wordSgt (.var 1) (word 0))
      (.ternary .wordAddMod (call 2 (.var 0)) (call 2 (.var 1)) (word 7))
      (.binary .wordSdiv (call 2 (.var 1)) (word 2))),
  .binary .wordShl (call 1 (call 2 (.var 0))) (call 2 (word 0))]

def mixedEntry : Wire.Expr :=
  .letE (call 1 (.var 0)) (.binary .wordXor (.var 0) (call 4 (call 3 (.var 1))))

private def originalChecks : IO Unit := do
  let graph ← checked mixedHelpers mixedEntry
  ensure (graph.program.check && functionHelpersAccepted graph.helpers)
    "mixed graph did not retain the whole checker boundary"
  let some restored := CheckedWordFunctionDAG.ofProgram? graph.program |
    throw (IO.userError "original mixed graph could not be readmitted")
  ensure (Wire.encodeProgram restored.program == Wire.encodeProgram graph.program)
    "readmission changed helper declaration order or entry"
  for (input, expected) in [(0, 11), (1, 6), (maximum, 1), (high, high / 2)] do
    observe graph input expected
  let source ← emitted graph
  ensure (source == (← emitted graph)) "call graph emission is nondeterministic"
  ensure (source.contractName == "SynthesizedCallGraphs" && source.methodName == "run" &&
    source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedCallGraphsDeploy"] &&
    source.runtimePath == ["SynthesizedCallGraphsDeploy", "SynthesizedCallGraphs"])
    "call graph wrapper metadata changed"
  ensure (CallGraph.emitterVersion == "solcore-source-call-graphs-v1" &&
    CallGraph.wrapperVersion == "solcore-word-call-graphs-contract-v1" &&
    CallGraph.selector == "0xa444f5e9") "call graph versions or ABI selector changed"
  -- A Bool condition may itself contain calls; only the selected branch calls
  -- its helper, and the new Word binder shifts the earlier-helper index.
  let branch : Wire.Expr := .ifE (.binary .wordEq (call 1 (.var 0)) (word 1))
    (.letE (word 7) (call 2 (.binary .wordAdd (.var 0) (.var 1))))
    (call 1 (call 1 (.var 0)))
  let branched ← checked [.binary .wordAdd (.var 0) (word 1)] branch
  observe branched 0 8
  observe branched 1 3
  observe branched maximum 1

private def primitiveChecks : IO Unit := do
  let c := call 1
  let fixtures : List (Wire.Expr × Nat × Nat) := [
    (.unary .wordClz (c (.var 0)), 0, 256),
    (.binary .wordDiv (c (.var 0)) (c (word 2)), 5, 2),
    (.binary .wordMod (c (.var 0)) (c (word 0)), maximum, 0),
    (.binary .wordShl (c (word 1)) (c (.var 0)), 255, high),
    (.binary .wordShr (c (word maximum)) (c (.var 0)), 256, 0),
    (.binary .wordSar (c (word high)) (c (.var 0)), maximum, maximum),
    (.binary .wordSdiv (c (.var 0)) (c (word maximum)), high, high),
    (.binary .wordSmod (c (.var 0)) (c (word 2)), maximum - 6, maximum),
    (.ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0), high - 1, 1),
    (.binary .wordByte (c (.var 0)) (c (word 0x1234)), 31, 0x34),
    (.binary .wordPow (c (word maximum)) (c (.var 0)), maximum, maximum),
    (.binary .wordSignExtend (c (word 0)) (c (.var 0)), 0x80, maximum - 0x7f),
    (.ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum)), maximum, 1),
    (.ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)), high, 1)]
  for (body, input, expected) in fixtures do
    let graph ← checked [.var 0] body
    ensure (CallGraphRenderer.supported body) "call graph excluded a primitive/call composition"
    let _ ← emitted graph
    observe graph input expected
  -- Every scalar primitive without a call must render exactly as its frozen
  -- primitive-profile counterpart, including raw snapshots and shift order.
  let mut expressions : List (Target × Wire.Expr) := []
  for operation in unaryOps do
    let operand := if operation == .boolNot then Wire.Expr.bool true else word 5
    expressions := expressions ++ [(Target.unaryResult operation, .unary operation operand)]
  for operation in binaryOps do
    expressions := expressions ++ [(Target.binaryResult operation, .binary operation (.var 0) (word 2))]
  for operation in ternaryOps do
    expressions := expressions ++ [(.word, .ternary operation (.var 0) (word 2) (word 7))]
  for (target, body) in expressions do
    let actual ← render ["sc_fn0"] target ["sc_input"] 4 7 body
    match PrimitiveRenderer.render target ["sc_input"] 4 7 body with
    | .ok expected =>
        ensure (actual.lines == expected.lines && actual.value == expected.value && actual.nextId == expected.nextId)
          "call-graph primitive formatting drifted from the primitive profile"
    | .error _ => throw (IO.userError "primitive compatibility fixture was unsupported")

private def formattingChecks : IO Unit := do
  let nested : Wire.Expr := .binary .wordShl (call 2 (call 1 (.var 0))) (call 1 (word 1))
  let result ← render ["near", "far"] .word ["input"] 4 0 nested
  ensure (result.lines == [
    "    let sc_v0: word = input;", "    let sc_v1: word = near(sc_v0);",
    "    let sc_v2: word = sc_v1;", "    let sc_v3: word = far(sc_v2);",
    "    let sc_v4: word = sc_v3;", "    let sc_v5: word = 1;",
    "    let sc_v6: word = sc_v5;", "    let sc_v7: word = near(sc_v6);",
    "    let sc_v8: word = sc_v7;", "    let sc_v9: word = sc_shl(sc_v8, sc_v4);"])
    "nested helper calls or raw shift operands changed evaluation order"
  let branch : Wire.Expr := .ifE (.binary .wordSgt (call 1 (.var 0)) (word 0))
    (.letE (word 7) (call 2 (.var 0))) (call 1 (word 9))
  let result ← render ["sc_fn0"] .word ["input"] 4 0 branch
  ensure (result.lines == [
    "    let sc_v0: word = input;", "    let sc_v1: word = sc_fn0(sc_v0);",
    "    let sc_v2: word = sc_v1;", "    let sc_v3: word = 0;", "    let sc_v4: word = sc_v3;",
    "    let sc_v5: bool = tobool(sc_sgt(sc_v2, sc_v4));", "    let sc_v6: word = 0;",
    "    if (sc_v5) {", "        let sc_v7: word = 7;", "        let sc_v8: word = sc_v7;",
    "        let sc_v9: word = sc_v8;", "        let sc_v10: word = sc_fn0(sc_v9);",
    "        sc_v6 = sc_v10;", "    } else {", "        let sc_v11: word = 9;",
    "        let sc_v12: word = sc_v11;", "        let sc_v13: word = sc_fn0(sc_v12);",
    "        sc_v6 = sc_v13;", "    }"])
    "branch-local helper calls escaped their branch or changed binder scope"
  let identity ← emitted (← checked [.var 0] (call 1 (.var 0)))
  ensure (identity.source == String.intercalate "\n" [
    "import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, "",
    "function sc_fn0(sc_arg: word) returns (word) {", "    return sc_arg;", "}", "",
    "contract SynthesizedCallGraphs {", "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);", "        let sc_v0: word = sc_input;",
    "        let sc_v1: word = sc_fn0(sc_v0);", "        return uint256(sc_v1);", "    }", "}", ""])
    "named helper declaration or fixed ABI wrapper changed"

private def rejectionChecks : IO Unit := do
  for body in [(.var 1 : Wire.Expr), .apply (.var 0) (.var 0), .apply (.var 2) (.var 0),
      .apply (.lambda .word .word (.var 0)) (word 0), .newCell .word (word 0),
      .integer 0, .pair (word 0) (word 1)] do
    ensure (CheckedWordFunctionDAG.ofParts? [.var 0] body).isNone
      "closed scalar DAG accepted an escaping/local/host function or unsupported value"
  for helpers in [([] : List Wire.Expr), List.replicate 4 (.var 0),
      [call 1 (.var 0)], [.var 0, call 2 (.var 0)]] do
    ensure (CheckedWordFunctionDAG.ofParts? helpers (call 1 (.var 0))).isNone
      "DAG accepted an empty, oversized, recursive or forward dependency"
  for (target, body) in [(.word, call 0 (.var 0)), (.word, call 2 (.var 0)),
      (.bool, call 1 (.var 0)), (.word, .apply (.lambda .word .word (.var 0)) (word 0)),
      (.word, .newCell .word (word 0)), (.word, .binary .integerAdd (word 0) (word 1))] do
    match CallGraphRenderer.renderWithFunctions ["sc_fn0"] target ["input"] 4 0 body with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "standalone renderer accepted an unsupported callee or expression")
  match CallGraphRenderer.renderWithFunctions ["sc_fn0"] .word ["input"] 4 0 (.var 1) with
  | .error (.unboundLocal 1) => pure ()
  | _ => throw (IO.userError "helper escaped as a scalar value")

def testSourceCallGraphEmitter : IO Unit := do
  originalChecks
  primitiveChecks
  formattingChecks
  rejectionChecks

end Tests.SourceCallGraphEmitter
