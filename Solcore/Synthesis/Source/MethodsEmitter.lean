import Solcore.Synthesis.Core.ContractMethods
import Solcore.Synthesis.Source.AggregateRenderer
import Solcore.Synthesis.Stateful.MethodsExecution

/-! Emit the several-methods contract. Each method's step becomes the top-level
functions `sc_m{i}_fn{j}` and `sc_m{i}_step`, and each method a public function
of its name and `uint256` parameters, in declaration order, so the compiler
builds std's method tuple in the order the original Core contract dispatches.
A method's body follows the original Core protocol in order: the sum of its
arguments, the step, the writes of slots zero, one and `2 + i`, the reread sum
and the odd-input revert. Memory at zero is touched only before that revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Methods

open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ContractMethods (CheckedPlan resultSlot)
open Solcore.Synthesis.Stateful.MethodsExecution (Method)

def emitterVersion : String := "solcore-source-methods-v1"
def wrapperVersion : String := "solcore-word-methods-contract-v1"
def contractName : String := "SynthesizedMethods"
def deployPath : List String := ["SynthesizedMethodsDeploy"]
def runtimePath : List String := ["SynthesizedMethodsDeploy", "SynthesizedMethods"]

/-- The emitted source of a several-methods contract; its methods are the case's. -/
structure EmittedMethods where
  source : String
  contractName : String
  deployPath : List String
  runtimePath : List String
  deriving Repr, BEq

/-- Method `position`'s step: its helpers and its entry. -/
private def stepLines (position : Nat) (step : Aggregates.CheckedDAG) : Except EmitError (List String) := do
  let stem := "sc_m" ++ toString position
  let mut names : List String := []
  let mut lines : List String := []
  for (body, index) in step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := stem ++ "_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 step.entry
  let result ← AggregateRenderer.requireValue entry
  return lines ++ ["function " ++ stem ++ "_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", ""]

/-- Method `position`'s public function. -/
private def methodLines (position : Nat) (method : Method) : List String :=
  let arguments := (List.range method.arity).map fun index => "a" ++ toString index
  let input := if method.arity = 0 then "0" else
    " + ".intercalate (arguments.map fun argument => "Typedef.rep(" ++ argument ++ ")")
  let slot := toString (resultSlot position)
  ["    function " ++ method.name ++ "(" ++ ", ".intercalate (arguments.map (· ++ ": uint256")) ++
      ") public returns (uint256) {",
    "        let sc_input: word = " ++ input ++ ";",
    "        let sc_computed: word = sc_m" ++ toString position ++ "_step(sc_input + sload(0));",
    "        sstore(0, sc_computed);",
    "        sstore(1, sload(1) + 1);",
    "        sstore(" ++ slot ++ ", sc_computed);",
    "        let sc_result: word = sload(0) + sload(1) + sload(" ++ slot ++ ");",
    "        if ((sc_input & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);",
    "    }"]

def emit (plan : CheckedPlan) (methods : List Method) : Except EmitError EmittedMethods := do
  let bodies := plan.steps.flatMap fun step => step.helpers ++ [step.entry]
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"] bodies, ""]
  for (step, position) in plan.steps.zipIdx do
    lines := lines ++ (← stepLines position step)
  lines := lines ++ ["contract " ++ contractName ++ " {"]
  for (method, position) in methods.zipIdx do
    lines := lines ++ (if position = 0 then [] else [""]) ++ methodLines position method
  lines := lines ++ ["}"]
  return {source := String.intercalate "\n" lines ++ "\n", contractName, deployPath, runtimePath}

end Solcore.Synthesis.Source.Methods
