import Solcore.Synthesis.Core.WordFunctionDAG
import Solcore.Synthesis.Source.CallGraphRenderer
import Solcore.Synthesis.Source.PrimitiveEmitter

/-! Full scalar primitive emission for checked acyclic Word-function graphs. Helpers
keep their Core declaration order and can call only earlier declarations.
`ScalarMeaning.CallGraph.emit_source_meaning` relates the emitted text to the original Core result under an independent
source semantics; see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallGraph

open Solcore.Synthesis.Core (CheckedWordFunctionDAG)

def emitterVersion : String := "solcore-source-call-graphs-v1"
def wrapperVersion : String := "solcore-word-call-graphs-contract-v1"
def contractName : String := "SynthesizedCallGraphs"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedCallGraphsDeploy"]
def runtimePath : List String := ["SynthesizedCallGraphsDeploy", "SynthesizedCallGraphs"]

def helperName (index : Nat) : String := "sc_fn" ++ toString index

/-- Emit all helper bodies and the entry from the same checked Core graph.
Local temporaries are fresh within each function and cannot shadow helper names. -/
def emit (graph : CheckedWordFunctionDAG) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""]
  for (body, index) in graph.helpers.zipIdx do
    let rendered ← CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 body
    let name := helperName index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""]
    names := name :: names
  let entry ← CallGraphRenderer.renderWithFunctions names .word ["sc_input"] 8 0 graph.entry
  lines := lines ++ ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
    ["        return uint256(" ++ entry.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.CallGraph
