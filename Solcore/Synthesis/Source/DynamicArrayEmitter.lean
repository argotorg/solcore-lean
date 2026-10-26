import Solcore.Synthesis.Core.DynamicArray
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed dynamic-array protocol. The ABI parameter is a lazily decoded
calldata array, so `values.length()` reads the same length word as the Core
contract and `values[i]` decodes element `i` only inside the branch that the
length admits. The three element branches, the slot writes, the counter update
and the odd-flags revert follow the original Core contract in order. Memory at
zero is touched only before the terminal revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.DynamicArray

open Solcore.Synthesis.Core.DynamicArray (CheckedPlan)

def emitterVersion : String := "solcore-source-dynamic-array-v1"
def wrapperVersion : String := "solcore-word-dynamic-array-contract-v1"
def contractName : String := "SynthesizedDynamicArray"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256[])"
def selector : String := "0x9a94c44b"
def deployPath : List String := ["SynthesizedDynamicArrayDeploy"]
def runtimePath : List String := ["SynthesizedDynamicArrayDeploy", "SynthesizedDynamicArray"]

private def elementLines (index : Nat) : List String :=
  let i := toString index
  ["        if (sc_length > " ++ i ++ ") {",
    "            let sc_value" ++ i ++ ": word = Typedef.rep(values[uint256(" ++ i ++ ")]);",
    "            sc_acc = sc_step(sc_acc + sc_value" ++ i ++ ");",
    "            sstore(" ++ toString (index + 1) ++ ", sc_acc);",
    "        }"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    "import {sload, sstore, mstore, revert_} from std.opcodes;", ""]
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
    "    function " ++ methodName ++ "(flags: uint256, values: calldata<array<uint256>>) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_length: word = Typedef.rep(values.length());",
    "        let sc_acc: word = sload(0);"] ++
    ((List.range Solcore.Synthesis.Core.DynamicArray.maxElements).flatMap elementLines) ++ [
    "        sstore(0, sc_acc);",
    "        let sc_total: word = sload(4) + sc_length;",
    "        sstore(4, sc_total);",
    "        let sc_result: word = sload(0) + sload(4);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.DynamicArray
