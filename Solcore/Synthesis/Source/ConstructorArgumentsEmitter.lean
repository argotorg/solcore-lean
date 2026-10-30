import Solcore.Synthesis.Core.ConstructorArguments
import Solcore.Synthesis.Source.EnumArgumentEmitter

/-! Emit the constructor-argument protocol as a contract with one constructor
and one public method. The constructor takes the plan's parameters, which the
compiler's generated deployment code copies from the init code's suffix and
std decodes before the body runs, and writes the decoded record to slots 1 to
5: the marker 1, the leading Word, the second Word, a `bytes` value's length
and its chunks, or an enum's one-based constructor index and decoded Words.
An enum is declared, and matched with one arm per constructor, as for the
enum-argument profile; a `bytes` value's chunks are read with `mload` only when
its length exceeds their start, since std zeroes the decoded payload's padding
but nothing past it. The method `run(uint256 flags, uint256 input)` follows
the original Core runtime in order: the step over slot 0, the input and slots 1
to 5, the write of slot 0 and the odd-flags revert. Memory at zero is touched
only before the terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ConstructorArguments

open Solcore.Synthesis.Core.ConstructorArguments (CheckedPlan Parameters)
open Solcore.Synthesis.Source.EnumArgument (enumName typeLines armLines)

def emitterVersion : String := "solcore-source-constructor-arguments-v1"
def wrapperVersion : String := "solcore-constructor-arguments-contract-v1"
def contractName : String := "SynthesizedConstructorArguments"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedConstructorArgumentsDeploy"]
def runtimePath : List String := ["SynthesizedConstructorArgumentsDeploy", "SynthesizedConstructorArguments"]

/-- The constructor and its writes of the record. -/
def constructorLines : Parameters → List String
  | .none => ["    constructor() {", "        sstore(1, 1);", "    }"]
  | .word => ["    constructor(a: uint256) {", "        sstore(1, Typedef.rep(a));", "    }"]
  | .words => ["    constructor(a: uint256, b: uint256) {", "        sstore(1, Typedef.rep(a));",
      "        sstore(2, Typedef.rep(b));", "    }"]
  | .bytes => ["    constructor(a: uint256, payload: memory<bytes>) {",
      "        sstore(1, Typedef.rep(a));",
      "        let sc_data: word = Typedef.rep(payload);",
      "        let sc_length: word = mload(sc_data);",
      "        sstore(2, sc_length);",
      "        if (sc_length > 0) {",
      "            sstore(3, mload((sc_data + 32)));",
      "        }",
      "        if (sc_length > 32) {",
      "            sstore(4, mload((sc_data + 64)));",
      "        }",
      "    }"]
  | .enum shape => ["    constructor(a: uint256, value: " ++ enumName ++ ") {",
      "        sstore(1, Typedef.rep(a));",
      "        let sc_index: word = 0;",
      "        let sc_w0: word = 0;",
      "        let sc_w1: word = 0;",
      "        let sc_w2: word = 0;",
      "        match (value) {"] ++
      (shape.constructors.zipIdx.map fun (constructor, index) => armLines index constructor).flatten ++
      ["        }",
      "        sstore(2, sc_index);",
      "        sstore(3, sc_w0);",
      "        sstore(4, sc_w1);",
      "        sstore(5, sc_w2);",
      "    }"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let enumLines := match plan.parameters with
    | .enum shape => ["import * from std.Generic;", "import * from std.ABIGeneric;"] ++
        [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"]
          (plan.step.helpers ++ [plan.step.entry]), ""] ++ typeLines shape
    | _ => [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"]
          (plan.step.helpers ++ [plan.step.entry]), ""]
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++ enumLines
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
    "contract " ++ contractName ++ " {"] ++ constructorLines plan.parameters ++ ["",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_result: word = sc_step(((((((sload(0) + sc_input) + sload(1)) + sload(2)) + sload(3)) + sload(4)) + sload(5)));",
    "        sstore(0, sc_result);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.ConstructorArguments
