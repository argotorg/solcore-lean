import Solcore.Synthesis.Core.BytesReturn
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the bytes-return protocol as a public method returning `memory<bytes>`.
The method allocates three Words with std's `allocate_memory`, stores the
length and the two data Words and returns the pointer; std's dispatcher
ABI-encodes it with `abi_encode`, which copies the length and data and zeroes
the rest of the last Word. The second data Word rereads slot one after the
writes. Memory at zero is touched only before the terminal revert. No emitter
proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.BytesReturn

open Solcore.Synthesis.Core.BytesReturn (CheckedPlan)

def emitterVersion : String := "solcore-source-bytes-returns-v1"
def wrapperVersion : String := "solcore-bounded-bytes-returns-contract-v1"
def contractName : String := "SynthesizedBytesReturns"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256)"
def selector : String := "0x24b912e5"
def deployPath : List String := ["SynthesizedBytesReturnsDeploy"]
def runtimePath : List String := ["SynthesizedBytesReturnsDeploy", "SynthesizedBytesReturns"]

/-- The multiplier `K` as a hexadecimal literal. -/
def multiplierLiteral : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 Solcore.Synthesis.Core.BytesReturn.multiplier)

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
    "    function " ++ methodName ++
      "(flags: uint256, input: uint256, length: uint256) public returns (memory<bytes>) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_length: word = (Typedef.rep(length) % 65);",
    "        let sc_prior: word = sload(0);",
    "        let sc_last: word = sload(2);",
    "        let sc_result: word = sc_step((sc_prior + sc_input));",
    "        sstore(0, sc_result);",
    "        sstore(1, (sload(1) + 1));",
    "        sstore(2, sc_input);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        let sc_pointer: word = allocate_memory(96);",
    "        mstore(sc_pointer, sc_length);",
    "        mstore((sc_pointer + 32), (sc_result * " ++ multiplierLiteral ++ "));",
    "        mstore((sc_pointer + 64), ((sload(1) * " ++ multiplierLiteral ++ ") ^ sc_last));",
    "        return Typedef.abs(sc_pointer);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.BytesReturn
