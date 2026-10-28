import Solcore.Synthesis.Core.TupleReturn
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the tuple-return protocol as a public method whose return type is the
tuple of the plan's arity of uint256. The method returns a tuple expression,
which std's dispatcher ABI-encodes into one static head per Word; its second
Word rereads slot one after the writes. Memory at zero is touched only before
the terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.TupleReturn

open Solcore.Synthesis.Core.TupleReturn (CheckedPlan)

def emitterVersion : String := "solcore-source-tuple-returns-v1"
def wrapperVersion : String := "solcore-word-tuple-returns-contract-v1"
def contractName : String := "SynthesizedTupleReturns"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedTupleReturnsDeploy"]
def runtimePath : List String := ["SynthesizedTupleReturnsDeploy", "SynthesizedTupleReturns"]

/-- The method's return type: the tuple of `arity` uint256. -/
def returnType (arity : Nat) : String :=
  "(" ++ String.intercalate ", " (List.replicate arity "uint256") ++ ")"

/-- The returned tuple's elements in protocol order, cut to the arity. -/
def returnedWords (arity : Nat) : List String :=
  ["uint256(sc_result)", "uint256(sload(1))", "uint256(sc_prior)", "uint256(sc_last)"].take arity

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
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
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns " ++
      returnType plan.arity ++ " {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_prior: word = sload(0);",
    "        let sc_last: word = sload(2);",
    "        let sc_result: word = sc_step((sc_prior + sc_input));",
    "        sstore(0, sc_result);",
    "        sstore(1, (sload(1) + 1));",
    "        sstore(2, sc_input);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return (" ++ String.intercalate ", " (returnedWords plan.arity) ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.TupleReturn
