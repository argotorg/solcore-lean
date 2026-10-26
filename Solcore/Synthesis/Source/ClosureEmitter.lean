import Solcore.Synthesis.Core.ClosurePlan
import Solcore.Synthesis.Source.AggregateRenderer

/-! Source lambdas capture the current Word value of an outer local. Later
assignments exercise snapshot preservation, and a generic callable argument
forwards the second invocation. Only fixed local Word captures are admitted. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Closure

open Solcore.Synthesis.Core.Closure (CheckedPlan Variant)

def emitterVersion : String := "solcore-source-closures-v2"
def wrapperVersion : String := "solcore-word-closures-contract-v1"
def contractName : String := "SynthesizedClosures"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedClosuresDeploy"]
def runtimePath : List String := ["SynthesizedClosuresDeploy", "SynthesizedClosures"]

private def secondClosure : Variant → List String
  | .snapshot => [
      "        let sc_second: function (word) returns (word) = sc_first;"]
  | .independent => [
      "        let sc_second: function (word) returns (word) = lam (sc_arg: word) -> word {",
      "            return sc_cap + sc_arg;", "        };"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ ["",
    "function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {",
    "    return f(x);", "}", ""]
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
    "        let sc_cap: word = sc_step(sc_input);",
    "        let sc_first: function (word) returns (word) = lam (sc_arg: word) -> word {",
    "            return sc_cap + sc_arg;", "        };",
    "        sc_cap = sc_cap + 1;"] ++ secondClosure plan.variant ++ [
    "        sc_cap = sc_cap + 2;",
    "        let sc_a: word = sc_first(sc_input);",
    "        let sc_b: word = sc_apply(sc_second, sc_input + 1);",
    "        return uint256(3 * sc_a + sc_b + sc_cap);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Closure
