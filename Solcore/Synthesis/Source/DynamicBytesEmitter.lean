import Solcore.Synthesis.Core.DynamicBytes
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed bytes protocol. The pinned ABI decoder produces `bytes` only
in memory: it follows the head offset, copies the length Word and the payload
into fresh memory and zeroes the padding to a whole Word. The source therefore
reads chunk `k` as the zero-padded memory Word `mload(data + 32 + 32k)` and the
last payload byte through the unaligned Word that ends at it, whose low byte is
zero for an empty payload. The two chunk branches, the slot writes and the
odd-flags revert follow the original Core contract in order. Memory at zero is
touched only before the terminal revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.DynamicBytes

open Solcore.Synthesis.Core.DynamicBytes (CheckedPlan)

def emitterVersion : String := "solcore-source-dynamic-bytes-v1"
def wrapperVersion : String := "solcore-word-dynamic-bytes-contract-v1"
def contractName : String := "SynthesizedBytes"
def methodName : String := "run"
def methodSignature : String := "run(uint256,bytes)"
def selector : String := "0x220eb9b6"
def deployPath : List String := ["SynthesizedBytesDeploy"]
def runtimePath : List String := ["SynthesizedBytesDeploy", "SynthesizedBytes"]

private def chunkLines (index : Nat) : List String :=
  ["        if (sc_length > " ++ toString (32 * index) ++ ") {",
    "            sc_acc = sc_step(sc_acc + mload(sc_data + " ++ toString (32 * (index + 1)) ++ "));",
    "            sstore(" ++ toString (index + 1) ++ ", sc_acc);",
    "        }"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_", "mload", "calldatasize"]
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
    "    function " ++ methodName ++ "(flags: uint256, payload: memory<bytes>) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_data: word = Typedef.rep(payload);",
    "        let sc_length: word = mload(sc_data);",
    "        let sc_acc: word = sload(0);"] ++ chunkLines 0 ++ chunkLines 1 ++ [
    "        let sc_tail: word = mload(sc_data + sc_length) & 255;",
    "        sstore(0, sc_acc);",
    "        let sc_total: word = sload(3) + sc_length;",
    "        sstore(3, sc_total);",
    "        sstore(4, sc_tail);",
    "        let sc_result: word = sload(0) + sload(3) + sload(4) + calldatasize();",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.DynamicBytes
