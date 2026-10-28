import Solcore.Synthesis.Core.CallGraphLoop
import Solcore.Synthesis.Source.AssemblyLoopRenderer

/-! Source emission of a scalar call-graph loop plan as one inline Yul block:
the step's helpers as Yul functions and the loop as a Yul `for` loop in one of
five forms. The Core reference stays the plan's finite ordinal guards; no
emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyLoop

open Solcore.Core.Wire (Expr)
open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)
open AssemblyLoopRenderer (line)

def emitterVersion : String := "solcore-source-assembly-loops-v1"
def wrapperVersion : String := "solcore-word-assembly-loops-contract-v1"
def contractName : String := "SynthesizedAssemblyLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedAssemblyLoopsDeploy"]
def runtimePath : List String := ["SynthesizedAssemblyLoopsDeploy", "SynthesizedAssemblyLoops"]

/-- How the Yul `for` loop runs the step, and how helpers return. -/
inductive Form where
  /-- Bounded by the loop condition. -/
  | bounded
  /-- Exited by `break` from a constant condition. -/
  | breaks
  /-- Bounded by the mask from a zero-argument function, skipping the step with
  `continue` once the counter reaches the limit. -/
  | continues
  /-- Inside a two-argument function exited by `leave`; helpers return through
  `leave` from conditionals in tail position. -/
  | leaves
  /-- Helpers return two values, and a two-argument, two-result step function
  also advances the counter. -/
  | pair
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Form

def all : List Form := [.bounded, .breaks, .continues, .leaves, .pair]

def name : Form → String
  | .bounded => "for"
  | .breaks => "break"
  | .continues => "continue"
  | .leaves => "leave"
  | .pair => "pair"

def ofString? : String → Option Form
  | "for" => some .bounded
  | "break" => some .breaks
  | "continue" => some .continues
  | "leave" => some .leaves
  | "pair" => some .pair
  | _ => none

end Form

def helperName (index : Nat) : String := "sc_fn" ++ toString index

/-- The helpers as Yul functions in declaration order, their names nearest first
for later bodies, and the next free temporary. -/
def helperFunctions (form : Form) (bodies : List Expr) :
    Except EmitError (List String × List String × Nat) := do
  let mut names : List String := []
  let mut lines : List String := []
  let mut nextId := 0
  for (body, index) in bodies.zipIdx do
    let name := helperName index
    match form with
    | .leaves =>
        let (statements, next) ← AssemblyLoopRenderer.renderTail names ["sc_arg"] 16 nextId body
        lines := lines ++ [line 12 ("function " ++ name ++ "(sc_arg) -> sc_ret {")] ++ statements ++
          [line 12 "}"]
        nextId := next
    | .pair =>
        let rendered ← AssemblyLoopRenderer.render names true ["sc_arg"] 16 nextId body
        lines := lines ++ [line 12 ("function " ++ name ++ "(sc_arg) -> sc_ret, sc_aux {")] ++
          rendered.lines ++ [line 16 ("sc_ret := " ++ rendered.value), line 16 "sc_aux := sc_arg", line 12 "}"]
        nextId := rendered.nextId
    | _ =>
        let rendered ← AssemblyLoopRenderer.render names false ["sc_arg"] 16 nextId body
        lines := lines ++ [line 12 ("function " ++ name ++ "(sc_arg) -> sc_ret {")] ++ rendered.lines ++
          [line 16 ("sc_ret := " ++ rendered.value), line 12 "}"]
        nextId := rendered.nextId
    names := name :: names
  return (names, lines, nextId)

/-- The block after the helpers: the loop of the form around the entry, which
assigns `sc_out`. The Yul counter is independent of the Core ordinal guards. -/
def loopStatements (form : Form) (names : List String) (mask : Nat) (nextId : Nat) (entry : Expr) :
    Except EmitError (List String) := do
  let bound := toString mask
  let header := [line 12 ("let sc_limit := and(sc_input, " ++ bound ++ ")"), line 12 "let sc_acc := sc_input"]
  match form with
  | .leaves =>
      let step ← AssemblyLoopRenderer.render names false ["sc_ret"] 20 nextId entry
      return [line 12 "function sc_loop(sc_acc, sc_limit) -> sc_ret {", line 16 "sc_ret := sc_acc",
          line 16 "for { let sc_i := 0 } 1 { sc_i := add(sc_i, 1) } {",
          line 20 "if iszero(lt(sc_i, sc_limit)) { leave }"] ++ step.lines ++
        [line 20 ("sc_ret := " ++ step.value), line 16 "}", line 12 "}",
          line 12 ("sc_out := sc_loop(sc_input, and(sc_input, " ++ bound ++ "))")]
  | .pair =>
      let step ← AssemblyLoopRenderer.render names true ["sc_arg"] 16 nextId entry
      return [line 12 "function sc_iterate(sc_arg, sc_count) -> sc_ret, sc_next {"] ++ step.lines ++
        [line 16 ("sc_ret := " ++ step.value), line 16 "sc_next := add(sc_count, 1)", line 12 "}"] ++ header ++
        [line 12 "let sc_i := 0", line 12 "for { } lt(sc_i, sc_limit) { } {",
          line 16 "sc_acc, sc_i := sc_iterate(sc_acc, sc_i)", line 12 "}", line 12 "sc_out := sc_acc"]
  | _ =>
      let step ← AssemblyLoopRenderer.render names false ["sc_acc"] 16 nextId entry
      let (prelude, opening) := match form with
        | .breaks => ([], [line 12 "for { let sc_i := 0 } 1 { sc_i := add(sc_i, 1) } {",
            line 16 "if iszero(lt(sc_i, sc_limit)) { break }"])
        | .continues => ([line 12 "function sc_bound() -> sc_ret {", line 16 ("sc_ret := " ++ bound),
              line 12 "}"],
            [line 12 "for { let sc_i := 0 } lt(sc_i, sc_bound()) { sc_i := add(sc_i, 1) } {",
              line 16 "if iszero(lt(sc_i, sc_limit)) { continue }"])
        | _ => ([], [line 12 "for { let sc_i := 0 } lt(sc_i, sc_limit) { sc_i := add(sc_i, 1) } {"])
      return prelude ++ header ++ opening ++ step.lines ++
        [line 16 ("sc_acc := " ++ step.value), line 12 "}", line 12 "sc_out := sc_acc"]

def emit (form : Form) (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let (names, helpers, nextId) ← helperFunctions form plan.graph.helpers
  let statements ← loopStatements form names plan.mask nextId plan.graph.entry
  let lines := ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_out: word = 0;",
    "        assembly {"] ++ helpers ++ statements ++
    ["        }", "        return uint256(sc_out);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.AssemblyLoop
