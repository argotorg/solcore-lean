import Solcore.Synthesis.Source.AggregateCallGraphEmitter
import Solcore.Synthesis.Source.CallGraphEmitter
import Solcore.Test.SourceCallGraphEmitter
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec.Program

/-! Generation, composition shapes and exact source shape for graphs that
compose Word pairs, Word sums, projections and case payload scopes with helper
calls. Only original Core programs are executed here; these tests neither run
emitted source nor prove compiler meaning preservation. -/
set_option autoImplicit false

namespace Tests.SourceAggregateCallGraphEmitter
open Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def maximum : Nat := Word.maximum.val
private def high : Nat := 2 ^ 255

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def graph (helpers : List Wire.Expr) (entry : Wire.Expr) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers entry with
  | some value => pure value
  | none => throw (IO.userError "aggregate call graph fixture failed checked admission")

private def emitted (value : Aggregates.CheckedDAG) : IO EmittedProgram :=
  match AggregateCallGraph.emit value with
  | .ok source => pure source
  | .error error => throw (IO.userError s!"aggregate call graph emission failed: {reprStr error}")

private def observe (value : Aggregates.CheckedDAG) (input expected : Nat) : IO Unit := do
  let original := value.instantiate (Word.ofNatModulo input)
  ensure original.check "original applied aggregate graph failed Core typing"
  match original.toCore.runStateful 100000 with
  | .done (.word result) state =>
      ensure (result.val == expected) s!"original Core result {result.val} differs from {expected}"
      ensure state.isEmpty "immutable aggregates allocated a cell"
  | _ => throw (IO.userError "original Core aggregate graph did not complete")

/-- h0(x) = x + 1 and h1(x) = 4x + 1 through a let-bound pair of a call and a
product. The entry branches to a sum, cases on it, nests a case whose scrutinee
calls a helper on the payload, and projects a pair built around a call. -/
def allShapesHelpers : List Wire.Expr := [
  .binary .wordAdd (.var 0) (word 1),
  .letE (.pair (call 1 (.var 0)) (.binary .wordMul (.var 0) (word 3)))
    (.binary .wordAdd (.first (.var 0)) (.second (.var 0)))]

def allShapesEntry : Wire.Expr :=
  .letE (.ifE (.binary .wordGt (.var 0) (word 5)) (.inLeft .word (call 1 (.var 0))) (.inRight .word (.var 0)))
    (.caseE (.var 0)
      (.binary .wordAdd (call 4 (.var 0)) (.caseE (.inLeft .word (call 4 (.var 0))) (.var 0) (.var 0)))
      (call 3 (.first (.pair (.var 0) (call 4 (.var 0))))))

private def shapeChecks : IO Unit := do
  let value ← graph allShapesHelpers allShapesEntry
  ensure (AggregateCallGraph.graphWithinGrammar value && value.program.check) "fixture left the grammar"
  ensure (AggregateCallGraph.structuralShapes value == AggregateCallGraph.shapeCatalog)
    "the mixed graph no longer covers the exact ordered nine composition shapes"
  -- x > 5: 8x + 4 through the left payload; otherwise 4x + 1 through the right.
  for (input, expected) in [(0, 1), (1, 5), (2, 9), (255, 2044), (256, 2052),
      (maximum, maximum - 3), (high, 4), (high - 1, maximum - 3)] do
    observe value input expected
  -- Each shape is detected by its own minimal composition, nowhere else.
  let single : List (String × List Wire.Expr × Wire.Expr) := [
    ("pair-component-call", [.var 0], .first (.pair (call 1 (.var 0)) (word 2))),
    ("sum-payload-call", [.var 0], .letE (.inRight .word (call 1 (.var 0))) (word 3)),
    ("projected-call-argument", [.var 0], .letE (.pair (.var 0) (word 1)) (call 2 (.second (.var 0)))),
    ("case-scrutinee-call", [.var 0], .caseE (.ifE (.binary .wordEq (call 1 (.var 0)) (word 0))
      (.inLeft .word (word 1)) (.inRight .word (word 2))) (.var 0) (word 7)),
    ("case-branch-call", [.var 0], .caseE (.inLeft .word (.var 0)) (call 2 (.var 1)) (word 0)),
    ("payload-call-argument", [.var 0], .letE (call 1 (.var 0))
      (.caseE (.inRight .word (.var 0)) (word 0) (call 3 (.var 0)))),
    ("aggregate-let", [.var 0], .letE (.inLeft .word (.var 0)) (call 2 (.var 1))),
    ("aggregate-branch", [.var 0], .letE (call 1 (.var 0))
      (.first (.ifE (.bool true) (.pair (.var 0) (word 1)) (.pair (word 2) (.var 0))))),
    ("nested-case", [.var 0], .letE (call 1 (.var 0))
      (.caseE (.inLeft .word (.var 0)) (.caseE (.inRight .word (.var 0)) (.var 0) (.var 1)) (word 0)))]
  for (shape, helpers, entry) in single do
    let value ← graph helpers entry
    let found := AggregateCallGraph.structuralShapes value
    ensure (found.contains shape) s!"minimal fixture lost composition shape {shape}"
  ensure (AggregateCallGraph.structuralShapes (← graph [.var 0] (call 1 (.var 0)))).isEmpty
    "a scalar call graph claimed an aggregate composition"
  -- A call next to, rather than inside, an aggregate is not a composition.
  let adjacent ← graph [.var 0]
    (.binary .wordAdd (call 1 (.var 0)) (.first (.pair (.var 0) (word 1))))
  ensure (AggregateCallGraph.structuralShapes adjacent).isEmpty "adjacent call was counted as composed"
  -- An argument that names an outer local, not the payload, is not a payload call.
  let outer ← graph [.var 0] (.caseE (.inLeft .word (word 1)) (call 2 (.var 1)) (word 0))
  ensure (AggregateCallGraph.structuralShapes outer == ["case-branch-call"])
    "an outer local was mistaken for the case payload"

private def generationChecks : IO Unit := do
  let mut shapes : List String := []
  let mut features : List String := []
  for budget in [96, 192, 256] do
    for seed in List.range 96 do
      let request : AggregateCallGraph.Request := {seed := Seed.ofNat seed, maxProgramNodes := budget}
      match AggregateCallGraph.generate request with
      | .error error => throw (IO.userError s!"aggregate graph generation failed: {reprStr error}")
      | .ok generated =>
          let value := generated.function
          ensure (generated.nodeCount ≤ budget && value.program.check &&
            AggregateCallGraph.graphWithinGrammar value) "generated graph escaped budget, typing or grammar"
          ensure (generated.bodyBudgets.length == value.helpers.length + 1) "body budgets lost a body"
          match AggregateCallGraph.generate request with
          | .ok again => ensure (Wire.encodeProgram again.function.program == Wire.encodeProgram value.program &&
              again.finalSeed == generated.finalSeed) "aggregate graph generation is not deterministic"
          | .error _ => throw (IO.userError "repeated generation failed")
          shapes := (shapes ++ AggregateCallGraph.structuralShapes value).eraseDups
          features := (features ++ value.features).eraseDups
          let _ ← emitted value
  ensure (AggregateCallGraph.shapeCatalog.all shapes.contains) "generation census missed a composition shape"
  ensure (["pair", "first", "second", "inLeft", "inRight", "case", "functionCall", "let", "if",
      "ternary:Solcore.Core.Wire.TernaryOp.wordMulMod", "unary:Solcore.Core.Wire.UnaryOp.wordClz"].all features.contains)
    "generation census missed an aggregate or primitive feature"
  ensure (!features.contains "newCell" && !features.contains "unitLiteral") "generation produced a cell or Unit"
  ensure (AggregateCallGraph.generate {seed := Seed.ofNat 0, maxProgramNodes := 513} matches .error .budgetTooLarge)
    "oversized aggregate budget accepted"
  ensure (AggregateCallGraph.generate {seed := Seed.ofNat 0, maxProgramNodes := 12} matches .error .budgetTooSmall)
    "aggregate budget below one helper accepted"

/-- Scalar-only bodies must render exactly as in the call-graph profile. -/
private def compatibilityChecks : IO Unit := do
  let bodies : List (List String × Wire.Expr) := [
    (["near", "far"], .binary .wordShl (call 2 (call 1 (.var 0))) (call 1 (word 1))),
    (["sc_fn0"], .ifE (.binary .wordSgt (call 1 (.var 0)) (word 0)) (.letE (word 7) (call 2 (.var 0))) (call 1 (word 9))),
    (["sc_fn1", "sc_fn0"], .letE (call 1 (.var 0)) (.ternary .wordMulMod (.var 0) (call 3 (.var 1)) (word 7))),
    ([], .unary .wordClz (.binary .wordSdiv (.var 0) (.unary .wordNot (word 5))))]
  for (functions, body) in bodies do
    match AggregateCallGraphRenderer.render functions .word [.word "input"] 4 3 body,
        CallGraphRenderer.renderWithFunctions functions .word ["input"] 4 3 body with
    | .ok actual, .ok expected =>
        ensure (actual.lines == expected.lines && actual.value == expected.value && actual.nextId == expected.nextId)
          "scalar formatting drifted from the call-graph renderer"
    | _, _ => throw (IO.userError "scalar compatibility fixture was rejected")
  -- Every scalar helper of the call-graph emitter fixture renders identically.
  for (body, index) in Tests.SourceCallGraphEmitter.mixedHelpers.zipIdx do
    let names := (List.range index).reverse.map CallGraph.helperName
    match AggregateCallGraphRenderer.render names .word [.word "sc_arg"] 4 0 body,
        CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 body with
    | .ok actual, .ok expected =>
        ensure (actual.lines == expected.lines && actual.value == expected.value) "helper formatting drifted"
    | _, _ => throw (IO.userError "call-graph helper fixture was rejected")

private def sourceChecks : IO Unit := do
  let projected ← graph [.var 0] (.first (.pair (call 1 (.var 0)) (.var 0)))
  let source ← emitted projected
  ensure (source == (← emitted projected)) "aggregate call graph emission is nondeterministic"
  ensure (source.contractName == "SynthesizedAggregateCallGraphs" && source.methodName == "run" &&
    source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedAggregateCallGraphsDeploy"] &&
    source.runtimePath == ["SynthesizedAggregateCallGraphsDeploy", "SynthesizedAggregateCallGraphs"])
    "aggregate call graph wrapper metadata changed"
  ensure (AggregateCallGraph.emitterVersion == "solcore-source-aggregate-call-graphs-v1" &&
    AggregateCallGraph.wrapperVersion == "solcore-word-aggregate-call-graphs-contract-v1" &&
    AggregateCallGraph.selector == "0xa444f5e9") "aggregate call graph versions or ABI selector changed"
  ensure (source.source == String.intercalate "\n" [
    "import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, "",
    "function sc_fn0(sc_arg: word) returns (word) {", "    return sc_arg;", "}", "",
    "contract SynthesizedAggregateCallGraphs {", "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);", "        let sc_v0: word = sc_input;",
    "        let sc_v1: word = sc_fn0(sc_v0);", "        let sc_v2: (word, word) = (sc_v1, sc_input);",
    "        let sc_v3: word = 0;", "        match (sc_v2) {", "            case (sc_p4, sc_p5) {",
    "                sc_v3 = sc_p4;", "            }", "        }",
    "        return uint256(sc_v3);", "    }", "}", ""])
    "projection of a call pair or the fixed ABI wrapper changed"
  observe projected 9 9
  -- Payloads extend scope before every local; helpers follow the full context.
  let payload ← graph [.binary .wordAdd (.var 0) (word 1)]
    (.letE (.inRight .word (.var 0)) (.caseE (.var 0) (word 0) (call 3 (.var 0))))
  match AggregateCallGraphRenderer.render ["sc_fn0"] .word [.word "input"] 4 0 payload.entry with
  | .ok rendered =>
      ensure (rendered.lines == [
        "    let sc_v0: sum<word, word> = inr(input);", "    let sc_v1: sum<word, word> = sc_v0;",
        "    let sc_v2: word = 0;", "    match (sc_v1) {", "        case inl(sc_p3) {",
        "            let sc_v4: word = 0;", "            sc_v2 = sc_v4;", "        }",
        "        case inr(sc_p5) {", "            let sc_v6: word = sc_p5;",
        "            let sc_v7: word = sc_fn0(sc_v6);", "            sc_v2 = sc_v7;", "        }", "    }"])
        "case payload scope, helper index or branch-local call changed"
  | .error error => throw (IO.userError s!"payload fixture rendering failed: {reprStr error}")
  observe payload 41 42

private def rejectionChecks : IO Unit := do
  let celled ← graph [.var 0] (.letE (.newCell .word (.var 0)) (call 2 (.loadCell (.var 0))))
  ensure (!AggregateCallGraph.graphWithinGrammar celled) "private cells entered the composition grammar"
  ensure (!(AggregateCallGraph.emit celled).toBool) "renderer accepted a private cell"
  let unit ← graph [.var 0] (.letE .unit (call 2 (.var 1)))
  ensure (!AggregateCallGraph.graphWithinGrammar unit) "Unit entered the composition grammar"
  match AggregateCallGraphRenderer.render [] .word [.wordPair "pair"] 4 0 (.var 0) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "renderer used a pair local as a Word")
  match AggregateCallGraphRenderer.render ["sc_fn0"] .word [.word "input"] 4 0 (.var 1) with
  | .error (.unboundLocal 1) => pure ()
  | _ => throw (IO.userError "helper escaped as a scalar value")
  for body in [(.first (.var 0) : Wire.Expr), .caseE (.var 0) (word 0) (word 1),
      .apply (.var 2) (.var 0), .pair (.var 0) (.pair (word 0) (word 1))] do
    ensure (Aggregates.CheckedDAG.ofParts? [.var 0] body).isNone "ill-typed aggregate composition was admitted"

def testSourceAggregateCallGraphEmitter : IO Unit := do
  shapeChecks
  generationChecks
  compatibilityChecks
  sourceChecks
  rejectionChecks

end Tests.SourceAggregateCallGraphEmitter
