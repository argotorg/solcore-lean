import Solcore.Synthesis.Core.WordFunctionDAG
import Solcore.Synthesis.Source.ScalarRenderer

/-! Named helper emission for checked acyclic Word-function graphs. Helpers
keep their Core declaration order and can call only earlier declarations.
The printer remains independently tested, not a proved compilation pass. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Function

open Solcore.Synthesis.Core (CheckedWordFunctionDAG)

def emitterVersion : String := "solcore-source-functions-v1"
def wrapperVersion : String := "solcore-word-functions-contract-v1"
def contractName : String := "SynthesizedFunctions"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedFunctionsDeploy"]
def runtimePath : List String := ["SynthesizedFunctionsDeploy", "SynthesizedFunctions"]

def helperName (index : Nat) : String := "sc_fn" ++ toString index

/-- Emit all helper bodies and the entry from the same checked Core graph.
Local temporaries are fresh within each function and cannot shadow helper names. -/
def emit (graph : CheckedWordFunctionDAG) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", ""]
  for (body, index) in graph.helpers.zipIdx do
    let rendered ← ScalarRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 body
    let name := helperName index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""]
    names := name :: names
  let entry ← ScalarRenderer.renderWithFunctions names .word ["sc_input"] 8 0 graph.entry
  lines := lines ++ ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
    ["        return uint256(" ++ entry.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Function
