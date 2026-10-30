import Solcore.Synthesis.Core.CallReturn
import Solcore.Synthesis.Source.AggregateRenderer
import Solcore.Synthesis.Source.EnumReturnEmitter

/-! Emit the call-return protocol as two sources with one contract each. The
child `SynthesizedReturnCallee` has one method `get(uint256 x)`: it follows the
original Core child in order, the step over `x` and slot 0, the writes of slots
0 and 1 and the odd-`x` revert of 32 bytes, then returns the plan's value. Typed,
the method declares the value's type and std's dispatcher encodes it; raw, it
declares `uint256`, writes the Words of the malformed encoding to memory and
ends with `return_`. A `bytes` value's data past its length are never read,
since std's encoder zero-pads them.

The parent `SynthesizedReturnCaller` has one method `run(uint256 target,
uint256 input)`. It writes `slot 0 + input` to slot 0, calls the target with
std's `raw_call` and the payload `0x9507d39a ‖ input`, and, when the call
succeeds, decodes the return data with std's `abi_decode` and
`MemoryWordReader` as the plan's type; otherwise it keeps the revert data's
first Word. It writes the flag and twice the size, the constructor index and
four Words to slots 1 to 6, sums them with slot 0, and reverts with the sum
under bit 1 of the input. Both sources declare the enum when the plan has one.
No emitter proof covers these wrappers. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallReturn

open Solcore.Synthesis.Core.CallReturn (CheckedPlan Kind Returned Delivery Cell Source)
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)

def emitterVersion : String := "solcore-source-call-returns-v1"
def wrapperVersion : String := "solcore-call-returns-contracts-v1"
def parentContractName : String := "SynthesizedReturnCaller"
def childContractName : String := "SynthesizedReturnCallee"
def parentMethodSignature : String := "run(uint256,uint256)"
def childMethodSignature : String := "get(uint256)"
def parentSelector : String := "0x7357f5d2"
def childSelector : String := "0x9507d39a"
def enumName : String := Solcore.Synthesis.Source.EnumReturn.enumName
def parentDeployPath : List String := [parentContractName ++ "Deploy"]
def parentRuntimePath : List String := [parentContractName ++ "Deploy", parentContractName]
def childDeployPath : List String := [childContractName ++ "Deploy"]
def childRuntimePath : List String := [childContractName ++ "Deploy", childContractName]

structure EmittedContracts where
  parentSource : String
  childSource : String
  deriving Repr, BEq

/-- A Word as a hexadecimal literal. -/
private def literal (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

private def multiplierLiteral : String := literal Solcore.Synthesis.Core.CallReturn.multiplier

/-- The enum's declaration, when the plan has one. -/
private def enumLines (kind : Kind) : List String :=
  match kind with
  | .enum shape =>
      ["enum " ++ enumName ++ " {"] ++
        shape.constructors.zipIdx.map (fun (constructor, index) =>
          "    " ++ Solcore.Synthesis.Source.EnumReturn.declaration constructor ++
            if index + 1 = shape.constructors.length then "" else ",") ++
        ["}", ""]
  | _ => []

private def stdImports (kind : Kind) : List String :=
  ["import * from std;", "import * from std.dispatch;"] ++
    match kind with
    | .enum _ => ["import * from std.Generic;", "import * from std.ABIGeneric;"]
    | _ => []

private def sourceName : Source → String
  | .r => "sc_r"
  | .c => "sc_c"
  | .x => "sc_x"
  | .o => "sc_o"
  | .d0 => "sc_d0"
  | .d1 => "sc_d1"

private def cellExpression : Cell → String
  | .const value => literal value.val
  | .value source kept =>
      if kept ≥ 32 then sourceName source
      else "(" ++ sourceName source ++ " & " ++ literal (Solcore.Synthesis.Core.CallReturn.keepMask kept) ++ ")"

/-- The declared return type of the child's method. -/
private def childReturnType (returned : Returned) : String :=
  match returned.delivery with
  | .raw _ => "uint256"
  | .typed => match returned.kind with
    | .tuple extra => "(" ++ ", ".intercalate (List.replicate (extra + 2) "uint256") ++ ")"
    | .bytes => "memory<bytes>"
    | .enum _ => enumName

/-- A `bytes` value of `length` bytes of `d0 ‖ d1`, bound to `sc_bytes`. -/
private def bytesLines (length : Nat) : List String :=
  ["        let sc_pointer: word = allocate_memory(96);",
    "        mstore(sc_pointer, " ++ toString length ++ ");",
    "        mstore((sc_pointer + 32), sc_d0);",
    "        mstore((sc_pointer + 64), sc_d1);",
    "        let sc_bytes: memory<bytes> = Typedef.abs(sc_pointer);"]

private def valueLines (returned : Returned) : List String :=
  match returned.delivery with
  | .raw _ =>
      let cells := Solcore.Synthesis.Core.CallReturn.rawCells returned
      ["        let sc_p: word = allocate_memory(" ++ toString (32 * cells.length) ++ ");"] ++
        cells.zipIdx.map (fun (cell, index) =>
          "        mstore(" ++ (if index = 0 then "sc_p" else "(sc_p + " ++ toString (32 * index) ++ ")") ++ ", " ++
            cellExpression cell ++ ");") ++
        ["        return_(sc_p, " ++ toString (Solcore.Synthesis.Core.CallReturn.returnedCells returned).2 ++ ");",
          "        return uint256(0);"]
  | .typed => match returned.kind with
    | .tuple extra =>
        ["        return (" ++ ", ".intercalate
          ((["sc_r", "sc_c", "sc_x", "sc_o"].take (extra + 2)).map fun name => "uint256(" ++ name ++ ")") ++ ");"]
    | .bytes => bytesLines returned.length ++ ["        return sc_bytes;"]
    | .enum shape =>
        let constructor := Solcore.Synthesis.Core.CallReturn.chosen shape returned.choice
        let value := enumName ++ "." ++ constructor.name
        match constructor.payload with
        | .noWords => ["        return " ++ value ++ ";"]
        | .oneWord => ["        return " ++ value ++ "(uint256(sc_d0));"]
        | .twoWords => ["        return " ++ value ++ "(uint256(sc_d0), uint256(sc_d1));"]
        | .boundedBytes => bytesLines returned.length ++ ["        return " ++ value ++ "(sc_bytes);"]

/-- The parent's decoding of a returned call, as the plan's type. -/
private def bytesRecordLines (indent value : String) : List String :=
  [indent ++ "let sc_b: word = Typedef.rep(" ++ value ++ ");",
    indent ++ "sc_w0 = mload(sc_b);",
    indent ++ "if (sc_w0 > 0) {",
    indent ++ "    sc_w1 = mload((sc_b + 32));",
    indent ++ "}",
    indent ++ "if (sc_w0 > 32) {",
    indent ++ "    sc_w2 = mload((sc_b + 64));",
    indent ++ "}"]

private def armLines (index : Nat) (constructor : Constructor) : List String :=
  let indent := "                            "
  let case := "                        case " ++ enumName ++ "." ++ constructor.name
  let marker := indent ++ "sc_index = " ++ toString (index + 1) ++ ";"
  (match constructor.payload with
    | .noWords => [case ++ " {", marker]
    | .oneWord => [case ++ "(sc_a0) {", marker, indent ++ "sc_w0 = Typedef.rep(sc_a0);"]
    | .twoWords => [case ++ "(sc_a0, sc_a1) {", marker, indent ++ "sc_w0 = Typedef.rep(sc_a0);",
        indent ++ "sc_w1 = Typedef.rep(sc_a1);"]
    | .boundedBytes => [case ++ "(sc_blob) {", marker] ++ bytesRecordLines indent "sc_blob") ++
    ["                        }"]

private def decodeLines (kind : Kind) : List String :=
  let indent := "                    "
  match kind with
  | .tuple extra =>
      let count := extra + 2
      let names := (List.range count).map fun index => "sc_a" ++ toString index
      let types := ", ".intercalate (List.replicate count "uint256")
      [indent ++ "let sc_tuple: (" ++ types ++ ") = abi_decode(ret, @(" ++ types ++ "), @MemoryWordReader);",
        indent ++ "match (sc_tuple) {",
        indent ++ "    case (" ++ ", ".intercalate names ++ ") {"] ++
        names.zipIdx.map (fun (name, index) =>
          indent ++ "        sc_w" ++ toString index ++ " = Typedef.rep(" ++ name ++ ");") ++
        [indent ++ "    }", indent ++ "}"]
  | .bytes =>
      [indent ++ "let sc_bytes: memory<bytes> = abi_decode(ret, @memory<bytes>, @MemoryWordReader);"] ++
        bytesRecordLines indent "sc_bytes"
  | .enum shape =>
      [indent ++ "let sc_value: " ++ enumName ++ " = abi_decode(ret, @" ++ enumName ++ ", @MemoryWordReader);",
        indent ++ "match (sc_value) {"] ++
        (shape.constructors.zipIdx.map fun (constructor, index) => armLines index constructor).flatten ++
        [indent ++ "}"]

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let returned := plan.returned
  let mut names : List String := []
  let mut child := stdImports returned.kind ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "return_", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""] ++ enumLines returned.kind
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    child := child ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  child := child ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ childContractName ++ " {",
    "    function get(x: uint256) public returns (" ++ childReturnType returned ++ ") {",
    "        let sc_x: word = Typedef.rep(x);",
    "        let sc_o: word = sload(0);",
    "        let sc_c: word = (sload(1) + 1);",
    "        let sc_r: word = sc_step((sc_x + sc_o));",
    "        sstore(0, sc_r);",
    "        sstore(1, sc_c);",
    "        if ((sc_x & 1) == 1) {",
    "            mstore(0, sc_r);",
    "            revert_(0, 32);",
    "        }",
    "        let sc_d0: word = (sc_r * " ++ multiplierLiteral ++ ");",
    "        let sc_d1: word = ((sc_c * " ++ multiplierLiteral ++ ") ^ sc_x);"] ++
    valueLines returned ++ ["    }", "}"]
  let parent := stdImports returned.kind ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"] [], ""] ++
    enumLines returned.kind ++
    ["contract " ++ parentContractName ++ " {",
    "    function run(target: uint256, input: uint256) public returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        sstore(0, (sload(0) + sc_input));",
    "        let sc_payload: word = allocate_memory(68);",
    "        mstore(sc_payload, 36);",
    "        mstore((sc_payload + 32), " ++ literal (Solcore.Synthesis.Core.CallReturn.getSelector * 2 ^ 224) ++ ");",
    "        mstore((sc_payload + 36), sc_input);",
    "        let sc_data: memory<bytes> = Typedef.abs(sc_payload);",
    "        let sc_ok: word = 0;",
    "        let sc_size: word = 0;",
    "        let sc_index: word = 0;",
    "        let sc_w0: word = 0;",
    "        let sc_w1: word = 0;",
    "        let sc_w2: word = 0;",
    "        let sc_w3: word = 0;",
    "        match (raw_call(address(sc_target), uint256(0), sc_data)) {",
    "            case (ok, ret) {",
    "                sc_ok = frombool(ok);",
    "                let sc_ret: word = Typedef.rep(ret);",
    "                sc_size = mload(sc_ret);",
    "                if (sc_ok == 1) {"] ++ decodeLines returned.kind ++
    ["                }",
    "                if ((sc_ok == 0) && (sc_size > 31)) {",
    "                    sc_w0 = mload((sc_ret + 32));",
    "                }",
    "            }",
    "        }",
    "        sstore(1, (sc_ok + (2 * sc_size)));",
    "        sstore(2, sc_index);",
    "        sstore(3, sc_w0);",
    "        sstore(4, sc_w1);",
    "        sstore(5, sc_w2);",
    "        sstore(6, sc_w3);",
    "        let sc_sum: word = (((((sload(0) + sc_index) + sc_w0) + sc_w1) + sc_w2) + sc_w3);",
    "        if ((sc_input & 2) == 2) {",
    "            mstore(0, sc_sum);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_sum);",
    "    }",
    "}"]
  return {
    parentSource := String.intercalate "\n" parent ++ "\n"
    childSource := String.intercalate "\n" child ++ "\n"
  }

end Solcore.Synthesis.Source.CallReturn
