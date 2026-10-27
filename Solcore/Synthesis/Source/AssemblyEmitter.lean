import Solcore.Synthesis.Core.WordFunction
import Solcore.Synthesis.Source.AssemblyRenderer

/-! Source emission of the checked scalar Word functions of the primitive
profile partly or wholly as inline Yul. The whole-body forms assign the Solcore
result local from one `assembly` block; the operations form keeps Solcore
control flow. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Assembly

open Solcore.Synthesis.Core (CheckedWordFunction)
open AssemblyRenderer (Form)

def emitterVersion : String := "solcore-source-assembly-v1"
def wrapperVersion : String := "solcore-word-assembly-contract-v1"

/-- The G0 features `emit` renders in every form: every operator and form. -/
def featureSupport := AssemblyRenderer.support
def contractName : String := "SynthesizedAssembly"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedAssemblyDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyDeploy", "SynthesizedAssembly"]

/-- The function body's statements and the Solcore Word that `run` returns. -/
def body (form : Form) (function : CheckedWordFunction) : Except EmitError (List String × String) := do
  match form with
  | .operations =>
      let rendered ← AssemblyRenderer.renderOperations .word ["sc_input"] 8 0 function.body
      return (rendered.lines, rendered.value)
  | .switch | .branches =>
      let rendered ← AssemblyRenderer.renderYul (form == .branches) ["sc_input"] 12 0 function.body
      return (["        let sc_out: word = 0;", "        assembly {"] ++ rendered.lines ++
        ["            sc_out := " ++ rendered.value, "        }"], "sc_out")

def emit (form : Form) (function : CheckedWordFunction) : Except EmitError EmittedProgram := do
  let (statements, value) ← body form function
  let lines := ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ statements ++
    ["        return uint256(" ++ value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Assembly
