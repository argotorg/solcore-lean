import Solcore.Synthesis.Core.Recursion
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit an actual recursive source function, or two functions that call each
other, to the depth `input & mask`. Each function makes one call at depth
`d - 1` when `d > 0`, assigning its single result local in both branches of
one `if`; this implementation is separate from the finite ordinal guards of
the checked Core reference. The aggregate step DAG is emitted as `sc_step`, as
for loops. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Recursion

open Solcore.Synthesis.Core.Recursion (CheckedPlan Form)

def emitterVersion : String := "solcore-source-recursion-v1"
def wrapperVersion : String := "solcore-word-recursion-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedRecursion"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedRecursionDeploy"]
def runtimePath : List String := ["SynthesizedRecursionDeploy", "SynthesizedRecursion"]

/-- One recursive function: `recurse` is its body when `sc_depth > 0`. -/
private def recursive (name : String) (recurse : List String) : List String :=
  ["function " ++ name ++ "(sc_depth: word, sc_acc: word) returns (word) {",
    "    let sc_result: word = sc_acc;",
    "    if (sc_depth > 0) {"] ++ recurse.map ("        " ++ ·) ++
  ["    } else {", "        sc_result = sc_acc;", "    }", "    return sc_result;", "}", ""]

/-- The recursive functions of a form, and the one the contract calls. -/
def recursion (form : Form) : List String × String :=
  match form with
  | .tail =>
      (recursive "sc_rec" ["let sc_next: word = sc_step(sc_acc);", "sc_result = sc_rec((sc_depth - 1), sc_next);"],
        "sc_rec")
  | .nontail =>
      (recursive "sc_rec" ["let sc_inner: word = sc_rec((sc_depth - 1), sc_acc);",
        "let sc_stepped: word = sc_step(sc_inner);", "sc_result = (sc_stepped + sc_depth);"], "sc_rec")
  | .mutual =>
      (recursive "sc_even" ["let sc_next: word = sc_step(sc_acc);", "sc_result = sc_odd((sc_depth - 1), sc_next);"] ++
        recursive "sc_odd" ["let sc_next: word = (sc_acc + sc_depth);",
          "sc_result = sc_even((sc_depth - 1), sc_next);"], "sc_even")

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ [""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  let (functions, entryName) := recursion plan.form
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", ""] ++ functions ++
    ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_depth: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_out: word = " ++ entryName ++ "(sc_depth, sc_input);",
    "        return uint256(sc_out);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Recursion
