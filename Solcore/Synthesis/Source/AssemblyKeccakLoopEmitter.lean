import Solcore.Synthesis.Core.KeccakLoop
import Solcore.Synthesis.Source.AssemblyStorageForm

/-! Emit the Keccak-loop protocol with every storage access, entry hash and log
in inline Yul. The contract keeps the Keccak-loop profile's fields, `acc` at
slot zero and `entries` at base slot one, which fix the layout the blocks
address directly: the entry of `key` lies at `keccak256(1 ++ key)`, hashed
from a 64-byte buffer that the first block reserves from the free-memory
pointer. The loop is the source while loop around one Solcore step call; each
iteration reads its entry and slot zero into the step argument, writes the
result to the entry and then to slot zero, and logs it from the buffer with
the counter and the key as topics. After the loop one block forms the result
and reverts it from the buffer for odd flags. This implementation is separate
from the finite ordinal guards of the checked Core reference. No emitter proof
covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyKeccakLoop

open Solcore.Synthesis.Core.KeccakLoop (CheckedPlan)
open Solcore.Synthesis.Source.AssemblyStorage (Form)

def emitterVersion : String := "solcore-source-assembly-keccak-loops-v1"
def wrapperVersion : String := "solcore-word-assembly-keccak-loops-contract-v1"
def contractName : String := "SynthesizedAssemblyKeccakLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedAssemblyKeccakLoopsDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyKeccakLoopsDeploy", "SynthesizedAssemblyKeccakLoops"]

/-- The Word locals besides flags, input, limit and base, all declared before the loop. -/
def locals : Form → List String
  | .split => ["sc_counter", "sc_key", "sc_sum", "sc_value", "sc_result", "sc_ptr"]
  | .carried | .pipelined => ["sc_counter", "sc_key", "sc_slot", "sc_sum", "sc_value", "sc_result", "sc_ptr"]

/-- The key of the counter's iteration, then its entry slot hashed from the
buffer, at the given indentation. -/
def keyLines (indent : String) (keyMask : Nat) : List String := [
  indent ++ "sc_key := or(sc_base, and(sc_counter, " ++ toString keyMask ++ "))",
  indent ++ "mstore(sc_ptr, 1)",
  indent ++ "mstore(add(sc_ptr, 32), sc_key)"]

/-- The key, its entry slot in `sc_slot` and the step argument. -/
def readLines (indent : String) (keyMask : Nat) : List String :=
  keyLines indent keyMask ++ [
    indent ++ "sc_slot := keccak256(sc_ptr, 64)",
    indent ++ "sc_sum := add(add(sload(sc_slot), sload(0)), sc_input)"]

/-- The two writes and the log of the iteration's value. -/
def writeLines (indent slot : String) : List String := [
  indent ++ "sstore(" ++ slot ++ ", sc_value)",
  indent ++ "sstore(0, sc_value)",
  indent ++ "mstore(sc_ptr, sc_value)",
  indent ++ "log2(sc_ptr, 32, sc_counter, sc_key)"]

def loopLines (form : Form) (keyMask : Nat) : List String :=
  match form with
  | .split => [
      "        while (sc_limit > sc_counter) {",
      "            assembly {"] ++
      keyLines "                " keyMask ++ [
      "                sc_sum := add(add(sload(keccak256(sc_ptr, 64)), sload(0)), sc_input)",
      "            }",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {",
      "                mstore(sc_ptr, 1)",
      "                mstore(add(sc_ptr, 32), sc_key)"] ++
      writeLines "                " "keccak256(sc_ptr, 64)" ++ [
      "            }",
      "            sc_counter = (sc_counter + 1);",
      "        }"]
  | .carried => [
      "        while (sc_limit > sc_counter) {",
      "            assembly {"] ++
      readLines "                " keyMask ++ [
      "            }",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {"] ++
      writeLines "                " "sc_slot" ++ [
      "                sc_counter := add(sc_counter, 1)",
      "            }",
      "        }"]
  | .pipelined => [
      "        assembly {",
      "            if gt(sc_limit, sc_counter) {"] ++
      readLines "                " keyMask ++ [
      "            }",
      "        }",
      "        while (sc_limit > sc_counter) {",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {"] ++
      writeLines "                " "sc_slot" ++ [
      "                sc_counter := add(sc_counter, 1)",
      "                if gt(sc_limit, sc_counter) {"] ++
      readLines "                    " keyMask ++ [
      "                }",
      "            }",
      "        }"]

def emit (form : Form) (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let steps ← AssemblyStorage.stepLines plan.step
  let lines := AssemblyStorage.importLines plan.step ++ steps ++ [
    "contract " ++ contractName ++ " {",
    "    acc: word;",
    "    entries: mapping(word => word);",
    "",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_base: word = (sc_input & ~7);"] ++
    (locals form).map (fun name => "        let " ++ name ++ ": word = 0;") ++ [
    "        assembly {",
    "            sc_ptr := mload(64)",
    "            mstore(64, add(sc_ptr, 64))",
    "        }"] ++
    loopLines form plan.keyMask ++ [
    "        assembly {",
    "            sc_result := add(sload(0), sc_limit)",
    "            if and(sc_flags, 1) {",
    "                mstore(sc_ptr, sc_result)",
    "                revert(sc_ptr, 32)",
    "            }",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.AssemblyKeccakLoop
