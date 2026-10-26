import Solcore.Synthesis.Source.CallGraphLoopEmitter
import Solcore.Synthesis.Source.LoopEmitter
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec.Program

/-! Plan sealing, measured generation and exact source shape for bounded loops
over scalar call graphs. Only original Core programs are executed here; these
tests neither run emitted source nor prove compiler meaning preservation. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphLoopEmitter
open Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def maximum : Nat := Word.maximum.val
private def high : Nat := 2 ^ 255

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def graph (helpers : List Wire.Expr) (entry : Wire.Expr) : IO CheckedWordFunctionDAG :=
  match CheckedWordFunctionDAG.ofParts? helpers entry with
  | some value => pure value
  | none => throw (IO.userError "call graph fixture failed checked admission")

private def plan (function : CheckedWordFunctionDAG) (mask : Nat) : IO CheckedPlan :=
  match CheckedPlan.ofParts? function mask with
  | some value => pure value
  | none => throw (IO.userError "call-graph loop fixture failed plan admission")

private def emitted (value : CheckedPlan) : IO EmittedProgram :=
  match CallGraphLoop.emit value with
  | .ok source => pure source
  | .error error => throw (IO.userError s!"call-graph loop emission failed: {reprStr error}")

private def run (program : Wire.Program) : IO Word := do
  ensure program.check "applied Core program failed its checker"
  match program.toCore.runStateful 100000 with
  | .done (.word value) _ => pure value
  | _ => throw (IO.userError "original Core program did not return a Word")

private def observe (value : CheckedPlan) (input expected : Nat) : IO Unit := do
  let result ← run (value.instantiate (Word.ofNatModulo input))
  ensure (result.val == expected) s!"call-graph loop result {result.val} differs from {expected}"

/-- The finite ordinal reference must agree with repeated scalar applications
of the same graph. Both sides are original Core executions. -/
private def iterated (value : CheckedPlan) (input : Word) : IO Unit := do
  let mut accumulator := input
  for _ in List.range (input.bitAnd (Word.ofNatModulo value.mask)).val do
    accumulator ← run (value.graph.instantiate accumulator)
  ensure ((← run (value.instantiate input)) == accumulator)
    "bounded loop reference differs from repeated scalar graph applications"

private def sealingChecks : IO Unit := do
  let doubled ← graph [.binary .wordAdd (.var 0) (word 1)] (call 1 (.binary .wordMul (.var 0) (word 2)))
  let checked ← plan doubled 7
  ensure (Wire.encodeProgram checked.loop.step.program == Wire.encodeProgram checked.graph.program)
    "executed loop step differs from the scalar graph"
  ensure (Wire.encodeProgram checked.program ==
    Wire.encodeProgram (BoundedLoop.canonicalProgram checked.loop.step 7)) "plan is not the canonical loop"
  ensure (checked.program.check && checked.mask == 7) "sealed plan lost typing or mask"
  -- 2x + 1 for exactly input & 7 iterations; the maximum Word is a fixed point.
  for (input, expected) in [(0, 0), (1, 3), (3, 31), (7, 1023), (maximum, maximum), (high, high)] do
    observe checked input expected
  for mask in [2, 4, 5, 8, 15] do
    ensure (CheckedPlan.ofParts? doubled mask).isNone "loop plan admitted an unsupported mask"
  let three ← plan doubled 3
  match CheckedPlan.ofProgram? doubled.program 3 with
  | some restored =>
      ensure (Wire.encodeProgram restored.program == Wire.encodeProgram three.program)
        "program readmission changed the plan"
  | none => throw (IO.userError "scalar graph program was not readmitted")
  let aggregate : Wire.Program := {
    resultType := .function .word .word, dataDefinitions := []
    body := functionDAGExpression [.first (.pair (.var 0) (word 1))] (call 1 (.var 0))}
  ensure (CheckedPlan.ofProgram? aggregate 1).isNone "aggregate step escaped the scalar call graph"
  -- Raw shifts keep Core operand order through the loop: ((2x) >> 4) three times.
  let shifted ← plan (← graph [.binary .wordShl (.var 0) (word 1)]
    (.binary .wordShr (call 1 (.var 0)) (word 4))) 3
  observe shifted 0xF003 120
  observe shifted 257 32
  for input in [0, 1, 3, 7, 0xF003, maximum, high] do
    iterated shifted (Word.ofNatModulo input)
    iterated checked (Word.ofNatModulo input)

private def generationChecks : IO Unit := do
  let mut masks : List Nat := []
  for seed in List.range 64 do
    let request : CallGraphLoop.Request := {seed := Seed.ofNat seed, maxProgramNodes := 256}
    match CallGraphLoop.generate request with
    | .error error => throw (IO.userError s!"bounded loop generation failed: {reprStr error}")
    | .ok generated =>
        let value := generated.plan
        ensure (CallGraphLoop.generatedMasks.contains value.mask) "generated an imported-only mask"
        masks := (masks ++ [value.mask]).eraseDups
        let overhead := BoundedLoop.appliedOverhead value.mask
        ensure (generated.stepBudget == 256 - overhead && generated.step.maxProgramNodes == generated.stepBudget)
          "step budget did not subtract the measured loop overhead"
        ensure (generated.nodeCount == Wire.programNodes (value.graph.instantiate Word.zero) + overhead &&
          generated.nodeCount ≤ 256) "measured loop overhead or complete budget differs"
        ensure (Wire.encodeProgram value.graph.program == Wire.encodeProgram generated.step.function.program)
          "plan graph differs from its generated step"
        match CallGraphLoop.generate request with
        | .ok again => ensure (Wire.encodeProgram again.plan.program == Wire.encodeProgram value.program &&
            again.finalSeed == generated.finalSeed) "bounded loop generation is not deterministic"
        | .error _ => throw (IO.userError "repeated generation failed")
        for input in [0, 1, 3, 7, maximum, high] do
          iterated value (Word.ofNatModulo input)
  ensure (masks.length == 3) "consecutive seeds did not select all generated masks"
  ensure (CallGraphLoop.generate {seed := Seed.ofNat 0, maxProgramNodes := 513} matches .error .budgetTooLarge)
    "oversized loop budget accepted"
  ensure (CallGraphLoop.generate {seed := Seed.ofNat 0, maxProgramNodes := 38} matches .error .budgetTooSmall)
    "loop budget below every generated mask accepted"
  ensure (CallGraphLoop.minimumAppliedNodes 1 == 39 && CallGraphLoop.minimumAppliedNodes 7 == 111)
    "measured minimum loop programs changed"

private def sourceChecks : IO Unit := do
  let identity ← plan (← graph [.var 0] (call 1 (.var 0))) 1
  let source ← emitted identity
  ensure (source == (← emitted identity)) "call-graph loop emission is nondeterministic"
  ensure (source.contractName == "SynthesizedCallGraphLoops" && source.methodName == "run" &&
    source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedCallGraphLoopsDeploy"] &&
    source.runtimePath == ["SynthesizedCallGraphLoopsDeploy", "SynthesizedCallGraphLoops"])
    "call-graph loop wrapper metadata changed"
  ensure (CallGraphLoop.emitterVersion == "solcore-source-call-graph-loops-v1" &&
    CallGraphLoop.wrapperVersion == "solcore-word-call-graph-loops-contract-v1" &&
    CallGraphLoop.selector == "0xa444f5e9") "call-graph loop versions or ABI selector changed"
  ensure (source.source == String.intercalate "\n" [
    "import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, "",
    "function sc_fn0(sc_arg: word) returns (word) {", "    return sc_arg;", "}", "",
    "function sc_step(sc_arg: word) returns (word) {", "    let sc_v0: word = sc_arg;",
    "    let sc_v1: word = sc_fn0(sc_v0);", "    return sc_v1;", "}", "",
    "contract SynthesizedCallGraphLoops {",
    "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & 1);",
    "        let sc_acc: word = sc_input;",
    "        let sc_counter: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            sc_acc = sc_step(sc_acc);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        return uint256(sc_acc);", "    }", "}", ""])
    "named helper, sc_step or bounded while wrapper changed"
  -- Helpers and the entry use the call-graph renderer, including raw aliases.
  let shifted ← plan (← graph [.binary .wordShl (.var 0) (word 1)]
    (.binary .wordShr (call 1 (.var 0)) (word 4))) 3
  let text := (← emitted shifted).source
  let helper ← match CallGraphRenderer.renderWithFunctions [] .word ["sc_arg"] 4 0
      (.binary .wordShl (.var 0) (word 1)) with
    | .ok value => pure value
    | .error _ => throw (IO.userError "helper rendering failed")
  let step ← match CallGraphRenderer.renderWithFunctions ["sc_fn0"] .word ["sc_arg"] 4 0
      (.binary .wordShr (call 1 (.var 0)) (word 4)) with
    | .ok value => pure value
    | .error _ => throw (IO.userError "step rendering failed")
  let expectedPrefix := String.intercalate "\n" ([
    "import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, "",
    "function sc_fn0(sc_arg: word) returns (word) {"] ++ helper.lines ++
    ["    return " ++ helper.value ++ ";", "}", "", "function sc_step(sc_arg: word) returns (word) {"] ++
    step.lines ++ ["    return " ++ step.value ++ ";", "}", "", "contract SynthesizedCallGraphLoops {"])
  ensure (text.startsWith expectedPrefix && (text.splitOn "sc_shl(").length == 2 &&
    (text.splitOn "sc_shr(").length == 2 && (text.splitOn "(sc_input & 3);").length == 2)
    "helpers or step were not emitted by the call-graph renderer with raw aliases"
  -- The older aggregate loop emitter remains a separate, unchanged printer.
  let some legacy := Aggregates.CheckedDAG.ofParts? [.var 0] (call 1 (.var 0)) |
    throw (IO.userError "legacy loop step fixture failed")
  let some legacyPlan := BoundedLoop.CheckedPlan.ofParts? legacy 1 |
    throw (IO.userError "legacy loop plan fixture failed")
  match Loop.emit legacyPlan with
  | .ok legacySource =>
      ensure (legacySource.contractName == "SynthesizedLoops" &&
        (legacySource.source.splitOn Primitive.opcodeImport).length == 1)
        "legacy loop emitter changed contract or gained raw primitive imports"
  | .error _ => throw (IO.userError "legacy loop emitter rejected its fixture")

def testSourceCallGraphLoopEmitter : IO Unit := do
  sealingChecks
  generationChecks
  sourceChecks

end Tests.SourceCallGraphLoopEmitter
