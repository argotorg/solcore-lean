import Solcore.Synthesis.Core.ModulePlan
import Solcore.Synthesis.Source.AggregateRenderer

/-! Four source modules exercise imported generics, closure captures and
compile-time computation together. Every provider contributes to the public
result. The bundle retains the complete original constant and step sources;
the entry alias is only a compatibility view of case.sol. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Modules

open Solcore.Synthesis.Core.Modules (CheckedPlan)

def emitterVersion : String := "solcore-source-modules-v2"
def wrapperVersion : String := "solcore-word-modules-contract-v1"
def sourceBundleSchema : String := "solcore-lean.source-bundle.v1"
def contractName : String := "SynthesizedModules"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedModulesDeploy"]
def runtimePath : List String := ["SynthesizedModulesDeploy", "SynthesizedModules"]

structure SourceFile where
  path : String
  source : String
  deriving Repr, BEq

structure EmittedBundle where
  source : String
  entry : String
  files : List SourceFile
  contractName : String
  methodName : String
  methodSignature : String
  selector : String
  deployPath : List String
  runtimePath : List String
  deriving Repr, BEq

/-- Canonical transport representation. Replay compares all file contents,
not just the entry alias used by older single-file clients. -/
def bundleJson (bundle : EmittedBundle) : Lean.Json :=
  Lean.Json.mkObj [
    ("schema", .str sourceBundleSchema),
    ("entry", .str bundle.entry),
    ("files", .arr (bundle.files.map fun file => Lean.Json.mkObj [
      ("path", .str file.path), ("source", .str file.source)]).toArray)]

private def join (lines : List String) : String := String.intercalate "\n" lines ++ "\n"

private def commonSource (plan : CheckedPlan) : Except EmitError String := do
  let constant ← ScalarRenderer.render .word [] 4 0 plan.constant.program.body
  return join (["import * from std;",
    "export { sc_static, sc_constant, sc_apply, sc_select };", "",
    "function sc_static(comptime value: word) returns (comptime<word>) {",
    "    return value;", "}", "",
    "function sc_constant() returns (comptime<word>) {"] ++ constant.lines ++
    ["    return sc_static(" ++ constant.value ++ ");", "}", "",
    "function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {",
    "    return f(x);", "}", "",
    "function sc_select<a>(flag: bool, left: a, right: a) returns (a) {",
    "    if (flag) {", "        return left;", "    }", "    return right;", "}"])

private def leftSource (plan : CheckedPlan) : Except EmitError String := do
  let mut lines := ["import * from std;", "import { sc_apply } from common;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ ["export { sc_left };", ""]
  let mut names : List String := []
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  return join (lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "function sc_left(input: word, k: word) returns (word) {",
    "    let sc_cap: word = sc_step(input + k);",
    "    let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {",
    "        return sc_cap + sc_arg;", "    };",
    "    sc_cap = sc_cap + 1;",
    "    return sc_apply(sc_f, input) + sc_cap;", "}"])

private def rightSource : String := join [
  "import * from std;", "import { sc_apply } from common;", "export { sc_right };", "",
  "function sc_right(input: word, k: word) returns (word) {",
  "    let sc_cap: word = input ^ k;",
  "    let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {",
  "        return sc_cap + sc_arg;", "    };",
  "    sc_cap = sc_cap + 2;",
  "    return sc_apply(sc_f, input + 1) + sc_cap;", "}"]

private def entrySource : String := join [
  "import * from std;", "import * from std.dispatch;",
  "import { sc_constant, sc_select } from common;",
  "import { sc_left } from left;", "import { sc_right } from right;", "",
  "contract " ++ contractName ++ " {",
  "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_k: comptime<word> = sc_constant();",
  "        let sc_left_value: word = sc_left(sc_input, sc_k);",
  "        let sc_right_value: word = sc_right(sc_input, sc_k);",
  "        let sc_selected: word = sc_select((sc_input & 1) == 1, sc_left_value, sc_right_value);",
  "        return uint256(sc_selected + sc_left_value + 3 * sc_right_value + sc_k);",
  "    }", "}"]

def emit (plan : CheckedPlan) : Except EmitError EmittedBundle := do
  let common ← commonSource plan
  let left ← leftSource plan
  return {
    source := entrySource
    entry := "case.sol"
    files := [
      ⟨"case.sol", entrySource⟩, ⟨"common.sol", common⟩,
      ⟨"left.sol", left⟩, ⟨"right.sol", rightSource⟩]
    contractName, methodName, methodSignature, selector, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Modules
