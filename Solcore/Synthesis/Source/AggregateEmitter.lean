import Solcore.Synthesis.Source.AggregateRenderer

/-! Source pairs and sums remain internal to Word helper functions. The
original checked Core DAG supplies an independent runtime oracle; this emitter
does not claim a formal source-printing preservation theorem. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Aggregate

open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

def emitterVersion : String := "solcore-source-aggregates-v2"
def wrapperVersion : String := "solcore-word-aggregates-contract-v1"
def contractName : String := "SynthesizedAggregates"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedAggregatesDeploy"]
def runtimePath : List String := ["SynthesizedAggregatesDeploy", "SynthesizedAggregates"]

def emit (graph : CheckedDAG) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (graph.helpers ++ [graph.entry]) ++ [""]
  for (body, index) in graph.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_input"] 8 0 graph.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);"] ++ entry.lines ++
    ["        return uint256(" ++ result ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Aggregate
