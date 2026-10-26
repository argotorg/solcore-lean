import Solcore.Synthesis.Core.ForwardedCall
import Solcore.Synthesis.Source.NestedCallEmitter

/-! Emit a payable parent and a payable child for one value-forwarding raw
Word call. The parent reads its call value through the pinned `callvalue`
wrapper and forwards the explicit amount through the raw `call` wrapper; the
child reads the value it received the same way. Scratch buffers reserve memory
from the free pointer before use, and child return data must contain exactly
one Word. No logs are emitted. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ForwardedCall

open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)
open Solcore.Synthesis.Source.NestedCall (EmittedContracts)

def emitterVersion : String := "solcore-source-forwarded-value-v1"
def wrapperVersion : String := "solcore-word-forwarded-value-v1"
def parentContractName : String := "SynthesizedForwarder"
def childContractName : String := "SynthesizedRecipient"
def parentMethodSignature : String := "run(uint256,uint256,uint256)"
def selector : String := "0x24b912e5"
/-- The parent's endowment, 2^72, covers three forwards of the largest bank value. -/
def parentConstructorValue : String := toString (2 ^ 72 : Nat)
def childConstructorValue : String := "0"
def parentDeployPath : List String := ["SynthesizedForwarderDeploy"]
def parentRuntimePath : List String := ["SynthesizedForwarderDeploy", "SynthesizedForwarder"]
def childDeployPath : List String := ["SynthesizedRecipientDeploy"]
def childRuntimePath : List String := ["SynthesizedRecipientDeploy", "SynthesizedRecipient"]

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mload", "mstore", "calldataload", "gas", "call",
      "returndatasize", "return_", "revert_", "invalid", "callvalue as sc_callvalue"]
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
    "contract " ++ childContractName ++ " {",
    "    fallback() payable {",
    "        let sc_input: word = calldataload(0);",
    "        let sc_value: word = sc_callvalue();",
    "        let sc_old0: word = sload(0);", "        let sc_old1: word = sload(1);",
    "        let sc_computed: word = sc_step(sc_input + sc_value + sc_old0);",
    "        sstore(0, sc_computed);", "        sstore(1, sc_old1 + sc_value);",
    "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 32);",
    "        mstore(sc_ptr, sc_computed);",
    "        if ((sc_input & 1) == 1) {", "            revert_(sc_ptr, 32);", "        }",
    "        return_(sc_ptr, 32);", "    }", "}", "",
    "contract " ++ parentContractName ++ " {",
    "    constructor() payable {}",
    "    function run(target: uint256, input: uint256, amount: uint256) public payable returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_amount: word = Typedef.rep(amount);",
    "        let sc_before: word = sload(0) + sc_input + sc_callvalue();",
    "        sstore(0, sc_before);",
    "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 64);",
    "        mstore(sc_ptr, sc_input);",
    "        let sc_ok: word = call(gas(), sc_target, sc_amount, sc_ptr, 32, sc_ptr + 32, 32);",
    "        if (!(returndatasize() == 32)) {", "            invalid();", "        }",
    "        let sc_after: word = mload(sc_ptr + 32);",
    "        if (sc_ok == 0) {", "            sc_after = sc_after + 1;", "        }",
    "        sstore(1, sc_after);",
    "        let sc_result: word = sload(0) + sload(1);",
    "        if ((sc_input & 2) == 2) {",
    "            mstore(sc_ptr, sc_result);", "            revert_(sc_ptr, 32);", "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    parentContractName, childContractName, parentMethodSignature, selector,
    parentConstructorValue, childConstructorValue,
    parentDeployPath, parentRuntimePath, childDeployPath, childRuntimePath
  }

end Solcore.Synthesis.Source.ForwardedCall
