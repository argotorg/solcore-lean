import Solcore.Synthesis.Core.LoopClosure
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit an actual source while loop whose body creates a fresh closure with
`let`, capturing a loop-carried Word local, and applies it in the same
iteration after that local changes. This implementation is separate from the
finite ordinal guards and snapshot lambdas of the checked Core reference. The
aggregate step DAG is emitted as `sc_step`, as for loops. No emitter proof
covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.LoopClosure

open Solcore.Synthesis.Core.LoopClosure (CheckedPlan Capture)

def emitterVersion : String := "solcore-source-loop-closures-v1"
def wrapperVersion : String := "solcore-word-loop-closures-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedLoopClosures"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedLoopClosuresDeploy"]
def runtimePath : List String := ["SynthesizedLoopClosuresDeploy", "SynthesizedLoopClosures"]

/-- The loop body of a capture. -/
def body : Capture → List String
  | .accumulator => [
      "            let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {",
      "                return sc_step(sc_acc + sc_arg);", "            };",
      "            sc_acc = (sc_acc + 1);",
      "            sc_acc = (sc_f(sc_counter) + sc_acc);",
      "            sc_counter = (sc_counter + 1);"]
  | .counter => [
      "            let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {",
      "                return (sc_step(sc_arg) + sc_counter);", "            };",
      "            sc_counter = (sc_counter + 1);",
      "            sc_acc = sc_apply(sc_f, sc_acc);"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ ["",
    "function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {",
    "    return f(x);", "}", ""]
  for (helper, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 helper
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
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_acc: word = sc_input;",
    "        let sc_counter: word = 0;",
    "        while (sc_limit > sc_counter) {"] ++ body plan.capture ++ [
    "        }",
    "        return uint256(sc_acc);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.LoopClosure
