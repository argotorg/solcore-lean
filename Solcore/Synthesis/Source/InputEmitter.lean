import Solcore.Synthesis.Core.WordFunction
import Solcore.Synthesis.Source.ScalarRenderer

/-! Source emission for a checked scalar function with one runtime Word input.
The ABI wrapper is separate from G0. Source meaning preservation remains a
tested printer obligation, not a theorem of this module. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Input

open Solcore.Synthesis.Core (CheckedWordFunction)

def emitterVersion : String := "solcore-source-input-v1"
def wrapperVersion : String := "solcore-word-input-contract-v1"
def contractName : String := "SynthesizedInput"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedInputDeploy"]
def runtimePath : List String := ["SynthesizedInputDeploy", "SynthesizedInput"]

/-- One source is shared by every runtime input. The input is converted from
its ABI wrapper once, and occupies the outermost scalar binding. -/
def emit (function : CheckedWordFunction) : Except EmitError EmittedProgram := do
  let body ← ScalarRenderer.render .word ["sc_input"] 8 0 function.body
  let lines := ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ body.lines ++
    ["        return uint256(" ++ body.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Input
