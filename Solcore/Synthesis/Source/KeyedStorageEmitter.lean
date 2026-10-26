import Solcore.Synthesis.Core.KeyedStorage
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed keyed-storage protocol. The ABI key selects a full-width
slot; the key slot, its wrapping successor and counter slot zero are written in
the same order as the original Core contract. Odd original inputs revert after
all writes and rereads with the tentative sum encoded as exactly 32 bytes; even
inputs return that Word through the ABI. Memory at zero is touched only before
the terminal revert. The arbitrary checked aggregate entry is preserved. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.KeyedStorage

open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)

def emitterVersion : String := "solcore-source-keyed-storage-v2"
def wrapperVersion : String := "solcore-word-keyed-storage-contract-v1"
def contractName : String := "SynthesizedKeyedStorage"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedKeyedStorageDeploy"]
def runtimePath : List String := ["SynthesizedKeyedStorageDeploy", "SynthesizedKeyedStorage"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"]
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
    "    function " ++ methodName ++ "(key: uint256, input: uint256) public returns (uint256) {",
    "        let sc_key: word = Typedef.rep(key);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_old: word = sload(sc_key);",
    "        let sc_count: word = sload(0);",
    "        let sc_computed: word = sc_step(sc_input + sc_old);",
    "        sstore(sc_key, sc_computed);",
    "        sstore(sc_key + 1, sc_old);",
    "        sstore(0, sc_count + 1);",
    "        let sc_final_key: word = sload(sc_key);",
    "        let sc_final_next: word = sload(sc_key + 1);",
    "        let sc_final_count: word = sload(0);",
    "        let sc_result: word = sc_final_key + sc_final_next + sc_final_count;",
    "        if ((sc_input & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.KeyedStorage
