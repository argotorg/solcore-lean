import Solcore.Synthesis.Core.AssemblyMemory
import Solcore.Synthesis.Source.AssemblyRenderer

/-! Source emission of an inline Yul memory plan: one `assembly` block that
defines the step as a Yul function, takes its base from the free-memory
pointer without moving it, fills the 96-byte window, runs the schedule's
stages, final read and optional hash, and assigns the Solcore result local.
No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyMemory

open Solcore.Synthesis.Core (CheckedWordFunction)
open Solcore.Synthesis.Core.AssemblyMemory (Schedule Width)

def emitterVersion : String := "solcore-source-assembly-memory-v1"
def wrapperVersion : String := "solcore-word-assembly-memory-contract-v1"

/-- The G0 features the step's rendering supports: every operator and form. -/
def featureSupport := AssemblyRenderer.support
def contractName : String := "SynthesizedAssemblyMemory"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedAssemblyMemoryDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyMemoryDeploy", "SynthesizedAssemblyMemory"]

private def line (text : String) : String := "            " ++ text

/-- The window byte at `offset` from the base. -/
private def address (offset : Nat) : String :=
  if offset = 0 then "sc_base" else "add(sc_base, " ++ toString offset ++ ")"

private def readName (index : Nat) : String := "sc_m" ++ toString index

/-- The block's statements: the step function in the `switch` form of
`runtime-assembly`, the base and the prologue, each stage, the final read and
the optional hash. -/
def block (function : CheckedWordFunction) (schedule : Schedule) : Except EmitError (List String) := do
  let step ← AssemblyRenderer.renderYul false ["sc_arg"] 16 0 function.body
  let stages := schedule.stages.zipIdx.flatMap fun (stage, index) =>
    [line ("let " ++ readName index ++ " := mload(" ++ address stage.read ++ ")"),
     line ((match stage.width with | .word => "mstore(" | .byte => "mstore8(") ++ address stage.write ++
       ", sc_step(" ++ readName index ++ "))")]
  let final := readName schedule.stages.length
  let result := match schedule.hash with
    | none => [line ("sc_out := sc_step(" ++ final ++ ")")]
    | some hash =>
        [line ("let sc_h := keccak256(" ++ address hash.offset ++ ", " ++ toString hash.length ++ ")"),
         line ("sc_out := add(sc_step(" ++ final ++ "), sc_h)")]
  return [line "function sc_step(sc_arg) -> sc_ret {"] ++ step.lines ++
    [line ("    sc_ret := " ++ step.value), line "}",
     line "let sc_base := mload(64)", line "mstore(sc_base, sc_input)",
     line "mstore(add(sc_base, 32), sc_step(sc_input))", line "mstore(add(sc_base, 64), not(sc_input))"] ++
    stages ++ [line ("let " ++ final ++ " := mload(" ++ address schedule.final ++ ")")] ++ result

def emit (function : CheckedWordFunction) (schedule : Schedule) : Except EmitError EmittedProgram := do
  let statements ← block function schedule
  let lines := ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_out: word = 0;", "        assembly {"] ++ statements ++
    ["        }", "        return uint256(sc_out);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.AssemblyMemory
