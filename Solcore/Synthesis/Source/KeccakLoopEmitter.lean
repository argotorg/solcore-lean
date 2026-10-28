import Solcore.Synthesis.Core.KeccakLoop
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the Keccak-loop protocol as an actual source while loop. The contract
declares an `acc` field at slot zero and an `entries: mapping(word => word)`
field at base slot one; the source never computes a slot itself, since
indexing `entries[k]` goes through the pinned std, which hashes the base slot
followed by the key. The counter, key and value locals are declared before the
loop and assigned inside it. A 64-byte log buffer is reserved from the
free-memory pointer before the loop, and every iteration stores its value
there and calls the pinned `std.opcodes` wrapper `log2` with the counter and
the key as topics. This implementation is separate from the finite ordinal
guards of the checked Core reference. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.KeccakLoop

open Solcore.Synthesis.Core.KeccakLoop (CheckedPlan)

def emitterVersion : String := "solcore-source-keccak-loops-v1"
def wrapperVersion : String := "solcore-word-keccak-loops-contract-v1"
def contractName : String := "SynthesizedKeccakLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedKeccakLoopsDeploy"]
def runtimePath : List String := ["SynthesizedKeccakLoopsDeploy", "SynthesizedKeccakLoops"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["mload", "mstore", "revert_", "log2 as sc_log2"]
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
    "    acc: word;",
    "    entries: mapping(word => word);",
    "",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_base: word = (sc_input & ~7);",
    "        let sc_counter: word = 0;",
    "        let sc_key: word = 0;",
    "        let sc_value: word = 0;",
    "        let sc_ptr: word = mload(64);",
    "        mstore(64, (sc_ptr + 64));",
    "        while (sc_limit > sc_counter) {",
    "            sc_key = (sc_base | (sc_counter & " ++ toString plan.keyMask ++ "));",
    "            sc_value = sc_step(((entries[sc_key] + acc) + sc_input));",
    "            entries[sc_key] = sc_value;",
    "            acc = sc_value;",
    "            mstore(sc_ptr, sc_value);",
    "            sc_log2(sc_ptr, 32, sc_counter, sc_key);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        let sc_result: word = (acc + sc_limit);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(sc_ptr, sc_result);",
    "            revert_(sc_ptr, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.KeccakLoop
