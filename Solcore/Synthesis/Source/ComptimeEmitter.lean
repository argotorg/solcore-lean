import Solcore.Synthesis.Core.ComptimePlan
import Solcore.Synthesis.Source.AggregateRenderer

/-! Render the original closed G0 expression inside a genuine comptime-return
function. Its result passes a comptime parameter before materialization into the
runtime wrapper. The emitter never evaluates or substitutes that expression. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Comptime

open Solcore.Synthesis.Core.Comptime (CheckedPlan Variant)

def emitterVersion : String := "solcore-source-comptime-v1"
def wrapperVersion : String := "solcore-word-comptime-contract-v1"
def contractName : String := "SynthesizedComptime"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedComptimeDeploy"]
def runtimePath : List String := ["SynthesizedComptimeDeploy", "SynthesizedComptime"]

private def runtimeLines : Variant → List String
  | .offset => [
      "        let sc_result: word = sc_step(sc_input + sc_constant_value) + sc_constant_value;"]
  | .scale => [
      "        let sc_scale: word = sc_constant_value | 1;",
      "        let sc_result: word = sc_step(sc_input) * sc_scale + sc_constant_value;"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let constant ← ScalarRenderer.render .word [] 4 0 plan.constant.program.body
  let mut lines := ["import * from std;", "import * from std.dispatch;", "",
    "function sc_static(comptime value: word) returns (comptime<word>) {",
    "    return value;", "}", "",
    "function sc_constant() returns (comptime<word>) {"] ++ constant.lines ++
    ["    return sc_static(" ++ constant.value ++ ");", "}", ""]
  let mut names : List String := []
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
    "        let sc_constant_value: comptime<word> = sc_constant();"] ++ runtimeLines plan.variant ++
    ["        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Comptime
