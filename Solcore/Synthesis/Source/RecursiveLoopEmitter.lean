import Solcore.Synthesis.Core.RecursiveLoop
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit actual recursive source functions, as for `runtime-recursion`, in
which every frame with depth `e > 0` runs a while loop of `e & I` iterations,
with its trip count, counter and value declared in the frame. This
implementation is separate from the unrolled frame and inner ordinal guards of
the checked Core reference. The aggregate step DAG is emitted as `sc_step`, as
for loops. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.RecursiveLoop

open Solcore.Synthesis.Core.RecursiveLoop (CheckedPlan)
open Solcore.Synthesis.Core.Recursion (Form)

def emitterVersion : String := "solcore-source-recursive-loops-v1"
def wrapperVersion : String := "solcore-word-recursive-loops-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedRecursiveLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedRecursiveLoopsDeploy"]
def runtimePath : List String := ["SynthesizedRecursiveLoopsDeploy", "SynthesizedRecursiveLoops"]

/-- One recursive function: `recurse` is its body when `sc_depth > 0`. -/
private def recursive (name : String) (recurse : List String) : List String :=
  ["function " ++ name ++ "(sc_depth: word, sc_acc: word) returns (word) {",
    "    let sc_result: word = sc_acc;",
    "    if (sc_depth > 0) {"] ++ recurse.map ("        " ++ ·) ++
  ["    } else {", "        sc_result = sc_acc;", "    }", "    return sc_result;", "}", ""]

/-- The frame's while loop of `sc_depth & I` iterations over `value`. -/
private def loop (innerMask : Nat) (value update : String) : List String :=
  ["let sc_trips: word = (sc_depth & " ++ toString innerMask ++ ");", "let sc_j: word = 0;",
    "while (sc_trips > sc_j) {", "    " ++ value ++ " = " ++ update ++ ";", "    sc_j = (sc_j + 1);", "}"]

/-- The recursive functions of a form, and the one the contract calls. -/
def recursion (form : Form) (innerMask : Nat) : List String × String :=
  match form with
  | .tail =>
      (recursive "sc_rec" (["let sc_value: word = sc_acc;"] ++ loop innerMask "sc_value" "sc_step(sc_value)" ++
        ["sc_result = sc_rec((sc_depth - 1), sc_value);"]), "sc_rec")
  | .nontail =>
      (recursive "sc_rec" (["let sc_inner: word = sc_rec((sc_depth - 1), sc_acc);"] ++
        loop innerMask "sc_inner" "sc_step(sc_inner)" ++ ["sc_result = (sc_inner + sc_depth);"]), "sc_rec")
  | .mutual =>
      (recursive "sc_even" (["let sc_value: word = sc_acc;"] ++ loop innerMask "sc_value" "sc_step(sc_value)" ++
        ["sc_result = sc_odd((sc_depth - 1), sc_value);"]) ++
        recursive "sc_odd" (["let sc_value: word = sc_acc;"] ++ loop innerMask "sc_value" "(sc_value + sc_depth)" ++
          ["sc_result = sc_even((sc_depth - 1), sc_value);"]), "sc_even")

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
  let (functions, entryName) := recursion plan.form plan.innerMask
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", ""] ++ functions ++
    ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_depth: word = (sc_input & " ++ toString plan.depthMask ++ ");",
    "        let sc_out: word = " ++ entryName ++ "(sc_depth, sc_input);",
    "        return uint256(sc_out);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.RecursiveLoop
