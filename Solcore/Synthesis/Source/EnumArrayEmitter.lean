import Solcore.Synthesis.Core.EnumArray
import Solcore.Synthesis.Source.EnumArgumentEmitter

/-! Emit the enum-array protocol as a public method taking a calldata array of
a user enum and two indices. The source declares the struct and the enum as
for one enum argument; std derives their `Generic` and ABI instances, its
dispatcher checks the array's head before the body runs, and `items[first]`
and `items[second]` decode one element each on demand through std's
`abiArrayGet`. Each read matches its element with one arm per constructor in
declaration order, setting that element's one-based index and decoded Words as
for one enum argument. The step, the ten writes and the odd-flags revert follow
the original Core contract in order. Memory at zero is touched only before the
terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumArray

open Solcore.Synthesis.Core.EnumArgument (Constructor Shape)
open Solcore.Synthesis.Core.EnumArray (CheckedPlan)
open Solcore.Synthesis.Source.EnumArgument (enumName structName typeLines)

def emitterVersion : String := "solcore-source-enum-array-arguments-v1"
def wrapperVersion : String := "solcore-enum-array-arguments-contract-v1"
def contractName : String := "SynthesizedEnumArrays"
def methodName : String := "run"
def deployPath : List String := ["SynthesizedEnumArraysDeploy"]
def runtimePath : List String := ["SynthesizedEnumArraysDeploy", "SynthesizedEnumArrays"]

/-- The method selector as `0x` and eight hexadecimal digits. -/
def selectorText (shape : Shape) : String :=
  let digits := Nat.toDigits 16 (Solcore.Synthesis.Core.EnumArray.selector shape)
  "0x" ++ String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/-- Element `k`'s arm of constructor `index`: its pattern, the one-based index
and the decoded Words, in names suffixed by `k`. -/
def armLines (element index : Nat) (constructor : Constructor) : List String :=
  let k := toString element
  let value := "            case " ++ enumName ++ "." ++ constructor.name
  let marker := "                sc_index" ++ k ++ " = " ++ toString (index + 1) ++ ";"
  let words := ["                sc_x" ++ k ++ " = Typedef.rep(sc_a" ++ k ++ ");",
    "                sc_y" ++ k ++ " = Typedef.rep(sc_b" ++ k ++ ");"]
  (match constructor.payload with
    | .noWords => [value ++ " {", marker]
    | .oneWord => [value ++ "(sc_a" ++ k ++ ") {", marker, words.getD 0 ""]
    | .twoWords => [value ++ "(sc_a" ++ k ++ ", sc_b" ++ k ++ ") {", marker] ++ words
    | .pair => [value ++ "(" ++ structName ++ "(sc_a" ++ k ++ ", sc_b" ++ k ++ ")) {", marker] ++ words
    | .bytes => [value ++ "(sc_d" ++ k ++ ") {", marker,
        "                let sc_data" ++ k ++ ": word = Typedef.rep(sc_d" ++ k ++ ");",
        "                sc_x" ++ k ++ " = mload(sc_data" ++ k ++ ");",
        "                if (sc_x" ++ k ++ " > 0) {",
        "                    sc_y" ++ k ++ " = mload((sc_data" ++ k ++ " + 32));",
        "                }",
        "                if (sc_x" ++ k ++ " > 32) {",
        "                    sc_z" ++ k ++ " = mload((sc_data" ++ k ++ " + 64));",
        "                }"]) ++ ["            }"]

/-- The read of element `k` at the method's argument `argument`. -/
def readLines (shape : Shape) (element : Nat) (argument : String) : List String :=
  let k := toString element
  ["        let sc_index" ++ k ++ ": word = 0;", "        let sc_x" ++ k ++ ": word = 0;",
    "        let sc_y" ++ k ++ ": word = 0;", "        let sc_z" ++ k ++ ": word = 0;",
    "        let sc_value" ++ k ++ ": " ++ enumName ++ " = items[" ++ argument ++ "];",
    "        match (sc_value" ++ k ++ ") {"] ++
    (shape.constructors.zipIdx.map fun (constructor, index) => armLines element index constructor).flatten ++
    ["        }"]

/-- The step's argument after the prior slot zero, left to right as original
Core adds them: the length, then each element's index and three Words. -/
def summands : List String :=
  ["sc_count", "sc_index0", "sc_x0", "sc_y0", "sc_z0", "sc_index1", "sc_x1", "sc_y1", "sc_z1"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
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
    "    function " ++ methodName ++ "(flags: uint256, items: calldata<array<" ++ enumName ++
      ">>, first: uint256, second: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_count: word = Typedef.rep(items.length());"] ++
    readLines plan.shape 0 "first" ++ readLines plan.shape 1 "second" ++
    ["        let sc_result: word = sc_step(" ++ summands.foldl (fun sum term => "(" ++ sum ++ " + " ++ term ++ ")")
      "sload(0)" ++ ");",
    "        sstore(0, sc_result);",
    "        sstore(1, sc_count);",
    "        sstore(2, sc_index0);",
    "        sstore(3, sc_x0);",
    "        sstore(4, sc_y0);",
    "        sstore(5, sc_z0);",
    "        sstore(6, sc_index1);",
    "        sstore(7, sc_x1);",
    "        sstore(8, sc_y1);",
    "        sstore(9, sc_z1);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature := Solcore.Synthesis.Core.EnumArray.signature plan.shape,
    deployPath, runtimePath
  }

end Solcore.Synthesis.Source.EnumArray
