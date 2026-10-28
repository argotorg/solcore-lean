import Solcore.Synthesis.Core.EnumArgument
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the enum-argument protocol as a public method taking a user enum. The
source declares the struct `ScPair` when a constructor carries it, then
`SynthesizedEnum` with the shape's constructors; std derives their `Generic`
and ABI instances, and its dispatcher decodes the argument before the body
runs. The method matches the value with one arm per constructor in declaration
order, each setting the one-based index and the decoded Words; a struct's
fields are bound through `ScPair(a, b)`. A `bytes` arm reads the length with
`mload` from `Typedef.rep` and each of its two chunks only when the length
exceeds the chunk's start, since std zeroes the decoded payload's padding but
nothing past it. The step, the five writes and the odd-flags revert follow the
original Core contract in order. Memory at zero is touched only before the
terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumArgument

open Solcore.Synthesis.Core.EnumArgument (CheckedPlan Constructor Shape)

def emitterVersion : String := "solcore-source-enum-arguments-v1"
def wrapperVersion : String := "solcore-enum-arguments-contract-v1"
def contractName : String := "SynthesizedEnumArguments"
def enumName : String := "SynthesizedEnum"
def structName : String := "ScPair"
def methodName : String := "run"
def deployPath : List String := ["SynthesizedEnumArgumentsDeploy"]
def runtimePath : List String := ["SynthesizedEnumArgumentsDeploy", "SynthesizedEnumArguments"]

/-- The method selector as `0x` and eight hexadecimal digits. -/
def selectorText (shape : Shape) : String :=
  let digits := Nat.toDigits 16 shape.selector
  "0x" ++ String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/-- A constructor's declaration: its name and its fields' types. -/
def declaration (constructor : Constructor) : String :=
  constructor.name ++ match constructor.payload with
    | .noWords => ""
    | .oneWord => "(uint256)"
    | .twoWords => "(uint256, uint256)"
    | .pair => "(" ++ structName ++ ")"
    | .bytes => "(memory<bytes>)"

/-- The arm of constructor `index`: its pattern, the one-based index and the
decoded Words. -/
def armLines (index : Nat) (constructor : Constructor) : List String :=
  let value := "            case " ++ enumName ++ "." ++ constructor.name
  let marker := "                sc_index = " ++ toString (index + 1) ++ ";"
  let words := ["                sc_w0 = Typedef.rep(sc_a0);", "                sc_w1 = Typedef.rep(sc_a1);"]
  (match constructor.payload with
    | .noWords => [value ++ " {", marker]
    | .oneWord => [value ++ "(sc_a0) {", marker, words.getD 0 ""]
    | .twoWords => [value ++ "(sc_a0, sc_a1) {", marker] ++ words
    | .pair => [value ++ "(" ++ structName ++ "(sc_a0, sc_a1)) {", marker] ++ words
    | .bytes => [value ++ "(sc_b) {", marker,
        "                let sc_data: word = Typedef.rep(sc_b);",
        "                sc_w0 = mload(sc_data);",
        "                if (sc_w0 > 0) {",
        "                    sc_w1 = mload((sc_data + 32));",
        "                }",
        "                if (sc_w0 > 32) {",
        "                    sc_w2 = mload((sc_data + 64));",
        "                }"]) ++ ["            }"]

/-- The struct, when a constructor carries it, then the enum. -/
def typeLines (shape : Shape) : List String :=
  let constructors := shape.constructors
  (if shape.payloads.contains .pair then
      ["struct " ++ structName ++ " {", "    a: uint256;", "    b: uint256;", "}", ""]
    else []) ++
    ["enum " ++ enumName ++ " {"] ++
    constructors.zipIdx.map (fun (constructor, index) =>
      "    " ++ declaration constructor ++ if index + 1 = constructors.length then "" else ",") ++
    ["}", ""]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let constructors := plan.shape.constructors
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", "import * from std.Generic;",
    "import * from std.ABIGeneric;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""] ++ typeLines plan.shape
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
    "    function " ++ methodName ++ "(flags: uint256, value: " ++ enumName ++ ") public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_index: word = 0;",
    "        let sc_w0: word = 0;",
    "        let sc_w1: word = 0;",
    "        let sc_w2: word = 0;",
    "        match (value) {"] ++
    (constructors.zipIdx.map fun (constructor, index) => armLines index constructor).flatten ++
    ["        }",
    "        let sc_result: word = sc_step(((((sload(0) + sc_index) + sc_w0) + sc_w1) + sc_w2));",
    "        sstore(0, sc_result);",
    "        sstore(1, sc_index);",
    "        sstore(2, sc_w0);",
    "        sstore(3, sc_w1);",
    "        sstore(4, sc_w2);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature := plan.shape.signature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.EnumArgument
