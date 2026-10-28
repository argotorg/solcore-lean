import Solcore.Synthesis.Core.StorageLoop
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the storage-loop protocol as an actual source while loop. The counter,
slot and value locals are declared before the loop and assigned inside it, and
each iteration's slots are computed from the counter, so the slot written by
one iteration is read by the next through a different expression. This
implementation is separate from the finite ordinal guards with literal slots
of the checked Core reference. Memory at zero is touched only before the
terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageLoop

open Solcore.Synthesis.Core.StorageLoop (CheckedPlan)

def emitterVersion : String := "solcore-source-storage-loops-v1"
def wrapperVersion : String := "solcore-word-storage-loops-contract-v1"
def contractName : String := "SynthesizedStorageLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedStorageLoopsDeploy"]
def runtimePath : List String := ["SynthesizedStorageLoopsDeploy", "SynthesizedStorageLoops"]

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
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_counter: word = 0;",
    "        let sc_slot: word = 0;",
    "        let sc_value: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            sc_slot = (sc_counter + 2);",
    "            sc_value = sc_step(((((sload(0) + sload(1)) + sload((sc_slot - 1))) + sload(sc_slot)) + sc_input));",
    "            sstore(sc_slot, sc_value);",
    "            sstore(0, sc_value);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        sstore(1, (sload(1) + sc_limit));",
    "        let sc_result: word = (sload(0) + sload(1));",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.StorageLoop
