import Solcore.Synthesis.Core.StorageContract
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed two-slot storage protocol with an arbitrary checked step
entry. ABI validation belongs to the case boundary; this profile claims no
correspondence for malformed calldata. The source printer is tested separately
from the original Core contract and its checked host-runtime admission. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Storage

open Solcore.Synthesis.Core.StorageContract (CheckedPlan)

def emitterVersion : String := "solcore-source-storage-v1"
def wrapperVersion : String := "solcore-word-storage-contract-v1"
def contractName : String := "SynthesizedStorage"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedStorageDeploy"]
def runtimePath : List String := ["SynthesizedStorageDeploy", "SynthesizedStorage"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    "import {sload, sstore} from std.opcodes;", ""]
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
    "        let sc_old0: word = sload(0);",
    "        let sc_old1: word = sload(1);",
    "        let sc_computed: word = sc_step(sc_input + sc_old0);",
    "        sstore(0, sc_computed);",
    "        sstore(1, sc_old1 + 1);",
    "        let sc_final0: word = sload(0);",
    "        let sc_final1: word = sload(1);",
    "        return uint256(sc_final0 + sc_final1);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Storage
