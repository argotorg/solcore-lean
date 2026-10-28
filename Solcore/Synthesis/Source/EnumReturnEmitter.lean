import Solcore.Synthesis.Core.EnumReturn
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the enum-return protocol as a public method returning a user enum. The
source declares `SynthesizedEnum` with the shape's constructors, and the method
tests the choice against each constructor index but the last and returns that
constructor; std derives the enum's `Generic` and ABI instances, and its
dispatcher encodes the value with `abi_encode`. A `bytes` constructor allocates
three Words with std's `allocate_memory`, stores the length and the two data
Words and passes the pointer as a `memory<bytes>` local. The second data Word
rereads slot one after the writes. Memory at zero is touched only before the
terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumReturn

open Solcore.Synthesis.Core.EnumReturn (CheckedPlan Constructor)
open Solcore.ContractRuntime (EnumPayload)

def emitterVersion : String := "solcore-source-enum-returns-v1"
def wrapperVersion : String := "solcore-enum-returns-contract-v1"
def contractName : String := "SynthesizedEnumReturns"
def enumName : String := "SynthesizedEnum"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256,uint256)"
def selector : String := "0x15509d2b"
def deployPath : List String := ["SynthesizedEnumReturnsDeploy"]
def runtimePath : List String := ["SynthesizedEnumReturnsDeploy", "SynthesizedEnumReturns"]

/-- The multiplier `K` as a hexadecimal literal. -/
def multiplierLiteral : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 Solcore.Synthesis.Core.EnumReturn.multiplier)

/-- A constructor's declaration: its name and its fields' types. -/
def declaration (constructor : Constructor) : String :=
  constructor.name ++ match constructor.payload with
    | .noWords => ""
    | .oneWord => "(uint256)"
    | .twoWords => "(uint256, uint256)"
    | .boundedBytes => "(memory<bytes>)"

/-- The statements that return constructor `index`, indented by `indent`. A
`bytes` constructor's locals carry its index. -/
def returnLines (indent : String) (index : Nat) (constructor : Constructor) : List String :=
  let value := enumName ++ "." ++ constructor.name
  match constructor.payload with
  | .noWords => [indent ++ "return " ++ value ++ ";"]
  | .oneWord => [indent ++ "return " ++ value ++ "(uint256(sc_first));"]
  | .twoWords => [indent ++ "return " ++ value ++ "(uint256(sc_first), uint256(sc_second));"]
  | .boundedBytes =>
      let pointer := "sc_pointer" ++ toString index
      let bytes := "sc_bytes" ++ toString index
      [indent ++ "let " ++ pointer ++ ": word = allocate_memory(96);",
        indent ++ "mstore(" ++ pointer ++ ", sc_length);",
        indent ++ "mstore((" ++ pointer ++ " + 32), sc_first);",
        indent ++ "mstore((" ++ pointer ++ " + 64), sc_second);",
        indent ++ "let " ++ bytes ++ ": memory<bytes> = Typedef.abs(" ++ pointer ++ ");",
        indent ++ "return " ++ value ++ "(" ++ bytes ++ ");"]

/-- Each constructor but the last returns under its choice test; the last
returns unconditionally. -/
def completionLines (constructors : List Constructor) : List String :=
  (constructors.zipIdx.map fun (constructor, index) =>
    if index + 1 = constructors.length then returnLines "        " index constructor
    else ["        if (sc_choice == " ++ toString index ++ ") {"] ++
      returnLines "            " index constructor ++ ["        }"]).flatten

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let constructors := plan.shape.constructors
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", "import * from std.Generic;",
    "import * from std.ABIGeneric;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), "",
    "enum " ++ enumName ++ " {"] ++
    constructors.zipIdx.map (fun (constructor, index) =>
      "    " ++ declaration constructor ++ if index + 1 = constructors.length then "" else ",") ++
    ["}", ""]
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
    "    function " ++ methodName ++ "(flags: uint256, input: uint256, choice: uint256, length: uint256) " ++
      "public returns (" ++ enumName ++ ") {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_choice: word = (Typedef.rep(choice) % " ++ toString constructors.length ++ ");",
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
    "        let sc_first: word = (sc_result * " ++ multiplierLiteral ++ ");",
    "        let sc_second: word = ((sload(1) * " ++ multiplierLiteral ++ ") ^ sc_last);"] ++
    completionLines constructors ++ ["    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.EnumReturn
