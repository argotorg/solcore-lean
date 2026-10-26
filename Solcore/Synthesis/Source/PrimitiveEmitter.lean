import Solcore.Synthesis.Core.WordFunction
import Solcore.Synthesis.Source.PrimitiveRenderer

/-! Source emission for independently checked Word functions with the full
scalar Word primitive catalog. Existing scalar emitter behavior is unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Primitive

open Solcore.Synthesis.Core (CheckedWordFunction)

def emitterVersion : String := "solcore-source-primitives-v1"
def wrapperVersion : String := "solcore-word-primitives-contract-v1"
def contractName : String := "SynthesizedPrimitives"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedPrimitivesDeploy"]
def runtimePath : List String := ["SynthesizedPrimitivesDeploy", "SynthesizedPrimitives"]

/-- Use raw opcode imports: the public `std.addmod` and `std.mulmod` wrappers
revert for modulus zero, whereas these Core operations return zero. -/
def opcodeImport : String :=
  "import { div as sc_div, mod as sc_mod, shl as sc_shl, shr as sc_shr, sar as sc_sar, " ++
  "sdiv as sc_sdiv, smod as sc_smod, sgt as sc_sgt, addmod as sc_addmod, mulmod as sc_mulmod, " ++
  "clz as sc_clz, byte as sc_byte, exp as sc_exp, signextend as sc_signextend } from std.opcodes;"

def emit (function : CheckedWordFunction) : Except EmitError EmittedProgram := do
  let body ← PrimitiveRenderer.render .word ["sc_input"] 8 0 function.body
  let lines := ["import * from std;", "import * from std.dispatch;", opcodeImport, "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ body.lines ++
    ["        return uint256(" ++ body.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Primitive
