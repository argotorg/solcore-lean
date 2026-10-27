import Solcore.Synthesis.Core.NestedLoop
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit an actual source while loop whose body runs a second while loop. Both
counters, the inner bound and the accumulator are declared before the outer
loop and assigned inside it; this implementation is separate from the finite
ordinal guards of the checked Core reference. The aggregate step DAG is
emitted as `sc_step`, as for single loops. No emitter proof covers this
wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedLoop

open Solcore.Synthesis.Core.NestedLoop (CheckedPlan Bound)

def emitterVersion : String := "solcore-source-nested-loops-v1"
def wrapperVersion : String := "solcore-word-nested-loops-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedNestedLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedNestedLoopsDeploy"]
def runtimePath : List String := ["SynthesizedNestedLoopsDeploy", "SynthesizedNestedLoops"]

/-- The inner bound the wrapper assigns at the start of each outer iteration. -/
def innerBoundSource (plan : CheckedPlan) : String :=
  match plan.bound with
  | .input => "(sc_input & " ++ toString plan.inner ++ ")"
  | .counter => "((sc_i + 1) & " ++ toString plan.inner ++ ")"
  | .accumulator => "(sc_acc & " ++ toString plan.inner ++ ")"

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ [""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_outer: word = (sc_input & " ++ toString plan.outer ++ ");",
    "        let sc_acc: word = sc_input;",
    "        let sc_i: word = 0;",
    "        let sc_inner: word = 0;",
    "        let sc_j: word = 0;",
    "        while (sc_outer > sc_i) {",
    "            sc_inner = " ++ innerBoundSource plan ++ ";",
    "            sc_j = 0;",
    "            while (sc_inner > sc_j) {",
    "                sc_acc = sc_step(sc_acc);",
    "                sc_j = (sc_j + 1);",
    "            }",
    "            sc_i = (sc_i + 1);",
    "        }",
    "        return uint256(sc_acc);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.NestedLoop
