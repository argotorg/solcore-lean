import Solcore.Synthesis.Core.GenericPlan
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit a genuinely polymorphic source selector, instantiated by the typed
arguments at Word, product or sum. The Core reference is independently built
with a monomorphic closure. `ScalarMeaning.Generic.emit_source_meaning`
relates the emitted text to the original Core result under an independent
generic source semantics; see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Generic

open Solcore.Synthesis.Core.Generic (CheckedPlan Variant)

def emitterVersion : String := "solcore-source-generics-v2"
def wrapperVersion : String := "solcore-word-generics-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedGenerics"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedGenericsDeploy"]
def runtimePath : List String := ["SynthesizedGenericsDeploy", "SynthesizedGenerics"]

private def selectedResult : Variant → List String
  | .word => [
      "        let sc_selected: word = sc_select(sc_flag, sc_left_word, sc_right_word);",
      "        return uint256(sc_selected);"]
  | .pair => [
      "        let sc_left: (word, word) = (sc_left_word, sc_input);",
      "        let sc_right: (word, word) = (sc_right_word, sc_next);",
      "        let sc_selected: (word, word) = sc_select(sc_flag, sc_left, sc_right);",
      "        let sc_result: word = 0;",
      "        match (sc_selected) {",
      "            case (sc_first, sc_second) {",
      "                sc_result = sc_first + sc_second;",
      "            }", "        }",
      "        return uint256(sc_result);"]
  | .sum => [
      "        let sc_left: sum<word, word> = inl(sc_left_word);",
      "        let sc_right: sum<word, word> = inr(sc_right_word);",
      "        let sc_selected: sum<word, word> = sc_select(sc_flag, sc_left, sc_right);",
      "        let sc_result: word = 0;",
      "        match (sc_selected) {",
      "            case inl(sc_payload) {", "                sc_result = sc_payload;", "            }",
      "            case inr(sc_payload) {", "                sc_result = sc_payload + 1;", "            }",
      "        }", "        return uint256(sc_result);"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ ["",
    "function sc_select<a>(flag: bool, left: a, right: a) returns (a) {",
    "    if (flag) {", "        return left;", "    }", "    return right;", "}", ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_left_word: word = sc_step(sc_input);",
    "        let sc_next: word = sc_input + 1;",
    "        let sc_right_word: word = sc_step(sc_next);",
    "        let sc_flag: bool = ((sc_input & 1) == 1);"] ++ selectedResult plan.variant ++
    ["    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Generic
