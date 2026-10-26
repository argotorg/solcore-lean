import Solcore.Synthesis.Core.CallGraphLoop
import Solcore.Synthesis.Source.CallGraphRenderer
import Solcore.Synthesis.Source.PrimitiveEmitter

/-! Emit a bounded source while loop around a scalar call-graph step. Helpers
and the arbitrary entry use the call-graph renderer and raw primitive aliases;
the entry is always `sc_step`. The older aggregate loop emitter is unchanged.
`ScalarMeaning.CallGraphLoop.emit_source_meaning` relates the emitted text to
the original Core result under an independent fuel-indexed loop semantics; see
`docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallGraphLoop

open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)

def emitterVersion : String := "solcore-source-call-graph-loops-v1"
def wrapperVersion : String := "solcore-word-call-graph-loops-contract-v1"
def contractName : String := "SynthesizedCallGraphLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedCallGraphLoopsDeploy"]
def runtimePath : List String := ["SynthesizedCallGraphLoopsDeploy", "SynthesizedCallGraphLoops"]

def helperName (index : Nat) : String := "sc_fn" ++ toString index

/-- The source counter is independent of the Core ordinal guards. Each helper
and the step have fresh local temporaries that cannot shadow wrapper names. -/
def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, ""]
  for (body, index) in plan.graph.helpers.zipIdx do
    let rendered ← CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 body
    let name := helperName index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""]
    names := name :: names
  let entry ← CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 plan.graph.entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ entry.value ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_acc: word = sc_input;",
    "        let sc_counter: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            sc_acc = sc_step(sc_acc);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        return uint256(sc_acc);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.CallGraphLoop
