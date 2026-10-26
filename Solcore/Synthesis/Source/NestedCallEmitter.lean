import Solcore.Synthesis.Core.NestedCall
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit two contracts with one raw Word call, explicit value, ordered logs and
independent child/root rollback. Scratch buffers reserve memory from the free
pointer before use. Child return data must contain exactly one Word. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedCall

open Solcore.Synthesis.Core.NestedCall (CheckedPlan)

def emitterVersion : String := "solcore-source-nested-call-v2"
def wrapperVersion : String := "solcore-word-nested-call-v1"
def parentContractName : String := "SynthesizedCaller"
def childContractName : String := "SynthesizedCallee"
def parentMethodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def parentConstructorValue : String := "8"
def childConstructorValue : String := "0"
def parentDeployPath : List String := ["SynthesizedCallerDeploy"]
def parentRuntimePath : List String := ["SynthesizedCallerDeploy", "SynthesizedCaller"]
def childDeployPath : List String := ["SynthesizedCalleeDeploy"]
def childRuntimePath : List String := ["SynthesizedCalleeDeploy", "SynthesizedCallee"]

structure EmittedContracts where
  source : String
  parentContractName : String
  childContractName : String
  parentMethodSignature : String
  selector : String
  parentConstructorValue : String
  childConstructorValue : String
  parentDeployPath : List String
  parentRuntimePath : List String
  childDeployPath : List String
  childRuntimePath : List String
  deriving Repr, BEq

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mload", "mstore", "calldataload", "gas", "call",
      "returndatasize", "return_", "revert_", "invalid", "log1 as log1_"]
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
    "        let sc_old0: word = sload(0);", "        let sc_old1: word = sload(1);",
    "        let sc_computed: word = sc_step(sc_input + sc_old0);",
    "        sstore(0, sc_computed);", "        sstore(1, sc_old1 + 1);",
    "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 32);",
    "        mstore(sc_ptr, sc_computed);", "        log1_(sc_ptr, 32, 2);",
    "        if ((sc_input & 1) == 1) {", "            revert_(sc_ptr, 32);", "        }",
    "        return_(sc_ptr, 32);", "    }", "}", "",
    "contract " ++ parentContractName ++ " {",
    "    constructor() payable {}",
    "    function run(target: uint256, input: uint256) public returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_before: word = sload(0) + sc_input;",
    "        sstore(0, sc_before);",
    "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 64);",
    "        mstore(sc_ptr, sc_before);", "        log1_(sc_ptr, 32, 1);",
    "        let sc_value: word = 0;",
    "        if ((sc_input & 4) == 4) {", "            sc_value = 1;", "        }",
    "        mstore(sc_ptr, sc_input);",
    "        let sc_ok: word = call(gas(), sc_target, sc_value, sc_ptr, 32, sc_ptr + 32, 32);",
    "        if (!(returndatasize() == 32)) {", "            invalid();", "        }",
    "        let sc_after: word = mload(sc_ptr + 32);",
    "        if (sc_ok == 0) {", "            sc_after = sc_after + 1;", "        }",
    "        sstore(1, sc_after);",
    "        mstore(sc_ptr, sc_after);", "        log1_(sc_ptr, 32, 3);",
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

end Solcore.Synthesis.Source.NestedCall
