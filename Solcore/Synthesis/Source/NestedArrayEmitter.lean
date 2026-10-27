import Solcore.Synthesis.Core.NestedArray
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed nested-array protocol. The ABI parameter is a lazily decoded
`calldata<array<calldata<array<uint256>>>>`, so `values.length()` reads the
same outer length Word as the Core contract, `values[uint256(i)]` follows row
`i`'s offset only inside the branch that the outer length admits, and the
row's `length()` and `row[uint256(j)]` read its length and elements the same
way. The three row branches with their two element branches, the slot writes,
the counter updates and the odd-flags revert follow the original Core contract
in order. Memory at zero is touched only before the terminal revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedArray

open Solcore.Synthesis.Core.NestedArray (CheckedPlan maxRows maxColumns rowSlot cellSlot)

def emitterVersion : String := "solcore-source-nested-array-v1"
def wrapperVersion : String := "solcore-word-nested-array-contract-v1"
def contractName : String := "SynthesizedNestedArray"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256[][])"
def selector : String := "0x7095aff8"
def deployPath : List String := ["SynthesizedNestedArrayDeploy"]
def runtimePath : List String := ["SynthesizedNestedArrayDeploy", "SynthesizedNestedArray"]

private def cellLines (row column : Nat) : List String :=
  let i := toString row
  ["            if (sc_width" ++ i ++ " > " ++ toString column ++ ") {",
    "                sc_acc = sc_step(sc_acc + Typedef.rep(sc_row" ++ i ++ "[uint256(" ++ toString column ++ ")]));",
    "                sstore(" ++ toString (1 + maxColumns * row + column) ++ ", sc_acc);",
    "            }"]

private def rowLines (row : Nat) : List String :=
  let i := toString row
  ["        if (sc_rows > " ++ i ++ ") {",
    "            let sc_row" ++ i ++ ": calldata<array<uint256>> = values[uint256(" ++ i ++ ")];",
    "            let sc_width" ++ i ++ ": word = Typedef.rep(sc_row" ++ i ++ ".length());",
    "            sc_cells = sc_cells + sc_width" ++ i ++ ";"] ++
    (List.range maxColumns).flatMap (cellLines row) ++ ["        }"]

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
      "(flags: uint256, values: calldata<array<calldata<array<uint256>>>>) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_rows: word = Typedef.rep(values.length());",
    "        let sc_cells: word = 0;",
    "        let sc_acc: word = sload(0);"] ++ (List.range maxRows).flatMap rowLines ++ [
    "        sstore(0, sc_acc);",
    "        sstore(" ++ toString rowSlot ++ ", sload(" ++ toString rowSlot ++ ") + sc_rows);",
    "        sstore(" ++ toString cellSlot ++ ", sload(" ++ toString cellSlot ++ ") + sc_cells);",
    "        let sc_result: word = sload(0) + sload(" ++ toString rowSlot ++ ") + sload(" ++ toString cellSlot ++ ");",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.NestedArray
