import Solcore.Synthesis.Core.CallValue
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed call-value protocol. The constructor and `run` are payable,
so the dispatcher never rejects value. `run` reads the value with the pinned
`std.opcodes` wrapper `callvalue`, writes `step(input + value + slot0)` to slot
zero and adds the value to slot one, in the same order as the original Core
contract. Odd flags revert after both writes with the result encoded as exactly
32 bytes; even flags return it through the ABI. Memory at zero is touched only
before the terminal revert. The arbitrary checked aggregate entry is preserved. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallValue

open Solcore.Synthesis.Core.CallValue (CheckedPlan)

def emitterVersion : String := "solcore-source-call-value-v1"
def wrapperVersion : String := "solcore-word-call-value-contract-v1"
def contractName : String := "SynthesizedCallValue"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedCallValueDeploy"]
def runtimePath : List String := ["SynthesizedCallValueDeploy", "SynthesizedCallValue"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_", "callvalue as sc_callvalue"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
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
    "    constructor() payable {}",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public payable returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_value: word = sc_callvalue();",
    "        let sc_old: word = sload(0);",
    "        let sc_total: word = sload(1);",
    "        let sc_result: word = sc_step(sc_input + sc_value + sc_old);",
    "        sstore(0, sc_result);",
    "        sstore(1, sc_total + sc_value);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.CallValue
