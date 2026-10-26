import Solcore.Synthesis.Core.StorageMapping
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed Keccak-mapping protocol. The contract declares a `counter`
field at slot zero and an `entries: mapping(word => word)` field at base slot
one; the source never computes a slot itself. Indexing `entries[k]` goes
through the pinned std, which hashes the base slot followed by the key. The
entry reads and writes, the counter update, the rereads and the odd-flags
revert follow the original Core contract in order. Memory at zero is touched
only before the terminal revert, after the std's own hashing scratch use. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageMapping

open Solcore.Synthesis.Core.StorageMapping (CheckedPlan)

def emitterVersion : String := "solcore-source-keccak-mapping-v1"
def wrapperVersion : String := "solcore-word-keccak-mapping-contract-v1"
def contractName : String := "SynthesizedMapping"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256)"
def selector : String := "0x24b912e5"
def deployPath : List String := ["SynthesizedMappingDeploy"]
def runtimePath : List String := ["SynthesizedMappingDeploy", "SynthesizedMapping"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["mstore", "revert_"] (plan.step.helpers ++ [plan.step.entry]), ""]
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
    "    counter: word;",
    "    entries: mapping(word => word);",
    "",
    "    function " ++ methodName ++ "(flags: uint256, key: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_key: word = Typedef.rep(key);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_old: word = entries[sc_key];",
    "        entries[sc_key] = sc_step(sc_input + sc_old);",
    "        entries[sc_key + 1] = sc_old + 1;",
    "        counter = counter + 1;",
    "        let sc_result: word = entries[sc_key] + entries[sc_key + 1] + counter;",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.StorageMapping
