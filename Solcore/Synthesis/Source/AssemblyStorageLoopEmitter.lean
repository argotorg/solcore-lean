import Solcore.Synthesis.Core.StorageLoop
import Solcore.Synthesis.Source.AssemblyStorageForm

/-! Emit the storage-loop protocol with every storage access in inline Yul. The
loop is the source while loop of the storage-loop profile around one Solcore
step call; the `assembly` blocks read the slots `0`, `1`, `1 + i` and `2 + i`
into the Solcore step argument, write the result to slot `2 + i` and then to
slot zero, and after the loop add the limit to slot one, form the result and
revert it from memory at zero for odd flags. This implementation is separate
from the finite ordinal guards with literal slots of the checked Core
reference. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyStorageLoop

open Solcore.Synthesis.Core.StorageLoop (CheckedPlan)
open Solcore.Synthesis.Source.AssemblyStorage (Form)

def emitterVersion : String := "solcore-source-assembly-storage-loops-v1"
def wrapperVersion : String := "solcore-word-assembly-storage-loops-contract-v1"
def contractName : String := "SynthesizedAssemblyStorageLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedAssemblyStorageLoopsDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyStorageLoopsDeploy", "SynthesizedAssemblyStorageLoops"]

/-- The step argument of the iteration whose upper slot is `slot`. -/
def stepArgument (slot : String) : String :=
  "add(add(add(add(sload(0), sload(1)), sload(sub(" ++ slot ++ ", 1))), sload(" ++ slot ++ ")), sc_input)"

/-- The Word locals besides flags, input and limit, all declared before the loop. -/
def locals : Form → List String
  | .split => ["sc_counter", "sc_sum", "sc_value", "sc_result"]
  | .carried | .pipelined => ["sc_counter", "sc_slot", "sc_sum", "sc_value", "sc_result"]

def loopLines : Form → List String
  | .split => [
      "        while (sc_limit > sc_counter) {",
      "            assembly {",
      "                let sc_slot := add(sc_counter, 2)",
      "                sc_sum := " ++ stepArgument "sc_slot",
      "            }",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {",
      "                sstore(add(sc_counter, 2), sc_value)",
      "                sstore(0, sc_value)",
      "            }",
      "            sc_counter = (sc_counter + 1);",
      "        }"]
  | .carried => [
      "        while (sc_limit > sc_counter) {",
      "            assembly {",
      "                sc_slot := add(sc_counter, 2)",
      "                sc_sum := " ++ stepArgument "sc_slot",
      "            }",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {",
      "                sstore(sc_slot, sc_value)",
      "                sstore(0, sc_value)",
      "                sc_counter := add(sc_counter, 1)",
      "            }",
      "        }"]
  | .pipelined => [
      "        assembly {",
      "            if gt(sc_limit, sc_counter) {",
      "                sc_slot := add(sc_counter, 2)",
      "                sc_sum := " ++ stepArgument "sc_slot",
      "            }",
      "        }",
      "        while (sc_limit > sc_counter) {",
      "            sc_value = sc_step(sc_sum);",
      "            assembly {",
      "                sstore(sc_slot, sc_value)",
      "                sstore(0, sc_value)",
      "                sc_counter := add(sc_counter, 1)",
      "                if gt(sc_limit, sc_counter) {",
      "                    sc_slot := add(sc_counter, 2)",
      "                    sc_sum := " ++ stepArgument "sc_slot",
      "                }",
      "            }",
      "        }"]

def emit (form : Form) (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let steps ← AssemblyStorage.stepLines plan.step
  let lines := AssemblyStorage.importLines plan.step ++ steps ++ [
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");"] ++
    (locals form).map (fun name => "        let " ++ name ++ ": word = 0;") ++
    loopLines form ++ [
    "        assembly {",
    "            sstore(1, add(sload(1), sc_limit))",
    "            sc_result := add(sload(0), sload(1))",
    "            if and(sc_flags, 1) {",
    "                mstore(0, sc_result)",
    "                revert(0, 32)",
    "            }",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.AssemblyStorageLoop
