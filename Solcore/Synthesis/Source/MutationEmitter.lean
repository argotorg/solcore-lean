import Solcore.Synthesis.Source.MutationRenderer

/-! Source mutation uses only private Word locals. The same original Core DAG
drives the independent runtime result. `ScalarMeaning.Mutation.emit_source_meaning`
relates the emitted text to the original Core result under an independent
source semantics; see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Mutation

open Solcore.Synthesis.Core.LocalMutation (CheckedDAG)

def emitterVersion : String := "solcore-source-mutation-v1"
def wrapperVersion : String := "solcore-word-mutation-contract-v1"

/-- The G0 features `emit` renders, those of `MutationRenderer`. -/
def featureSupport := MutationRenderer.support
def contractName : String := "SynthesizedMutation"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedMutationDeploy"]
def runtimePath : List String := ["SynthesizedMutationDeploy", "SynthesizedMutation"]

def emit (graph : CheckedDAG) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", ""]
  for (body, index) in graph.helpers.zipIdx do
    let rendered ← MutationRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← MutationRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← MutationRenderer.render names .word [.word "sc_input"] 8 0 graph.entry
  let result ← MutationRenderer.requireValue entry
  lines := lines ++ ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
    ["        return uint256(" ++ result ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Mutation
