import Solcore.Synthesis.Core.BoundedLoop
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit an actual source while loop. Its counter implementation is separate
from the finite ordinal guards in the checked Core reference. Every arbitrary
aggregate-DAG entry is emitted as `sc_step`; the last helper is not assumed to
be the entry. Source-printing preservation is tested, not formally asserted. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Loop

open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)

def emitterVersion : String := "solcore-source-loops-v1"
def wrapperVersion : String := "solcore-word-loops-contract-v1"
def contractName : String := "SynthesizedLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedLoopsDeploy"]
def runtimePath : List String := ["SynthesizedLoopsDeploy", "SynthesizedLoops"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", ""]
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
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_acc: word = sc_input;",
    "        let sc_counter: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            sc_acc = sc_step(sc_acc);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        return uint256(sc_acc);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Loop
