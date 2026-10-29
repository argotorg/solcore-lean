import Solcore.Synthesis.Core.ArrayReturn
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the array-return protocol as a public method declared to return
`uint256`. After the protocol's writes it builds a `memory<DynArray<t>>` of
`length % 4` elements, encodes it with std's `abi_encode` and ends with the
`return_` opcode over the encoding, which is what std's dispatcher does after a
method returns (`do_exec`). The checked driver accepts this as written; it
refuses a declared array output (Q008).

The count and the inner lengths are read at run time, from `length` and from
the digits of `choice`, so that no optimizer can fold std's encoder loops; the
source depends only on the element type and the step. Element `i` is built
from `sc_rk + i` and `sc_mix + i`. A `bytes` element is a fresh 96-byte
allocation holding its length and both Words, so its memory past the length is
dirty; an inner array holds as many of the two Words as its length takes.
Memory at zero is touched only before the terminal revert. No emitter proof
covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ArrayReturn

open Solcore.Synthesis.Core.ArrayReturn (CheckedPlan Element)

def emitterVersion : String := "solcore-source-array-returns-v1"
def wrapperVersion : String := "solcore-array-returns-contract-v1"
def contractName : String := "SynthesizedArrayReturns"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256,uint256)"
def selector : String := "0x15509d2b"
def deployPath : List String := ["SynthesizedArrayReturnsDeploy"]
def runtimePath : List String := ["SynthesizedArrayReturnsDeploy", "SynthesizedArrayReturns"]

def multiplierLiteral : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 Solcore.Synthesis.Core.ArrayReturn.multiplier)

/-- The element's source type. -/
def elementType : Element → String
  | .words => "uint256"
  | .fourBytes => "bytes4"
  | .bytes => "memory<bytes>"
  | .nested => "memory<DynArray<uint256>>"

/-- Inner length `index` from `choice`: digit `index` of the element type's
base. -/
private def digit (element : Element) (index : Nat) : String :=
  let base := toString element.base
  if index = 0 then "(sc_choice % " ++ base ++ ")"
  else "((sc_choice / " ++ toString (element.base ^ index) ++ ") % " ++ base ++ ")"

/-- The statements that set element `index`, inside its count guard. -/
def elementLines (element : Element) (index : Nat) : List String :=
  let i := toString index
  let a := "(sc_rk + " ++ i ++ ")"
  let b := "(sc_mix + " ++ i ++ ")"
  let set := fun (value : String) => "            IndexAccess.set(sc_items, uint256(" ++ i ++ "), " ++ value ++ ");"
  match element with
  | .words => [set ("uint256(" ++ a ++ ")")]
  | .fourBytes => [
      "            let sc_tag" ++ i ++ ": bytes4 = Typedef.abs((" ++ a ++ " & 0xffffffff));",
      set ("sc_tag" ++ i)]
  | .bytes => [
      "            let sc_p" ++ i ++ ": word = allocate_memory(96);",
      "            mstore(sc_p" ++ i ++ ", " ++ digit element index ++ ");",
      "            mstore((sc_p" ++ i ++ " + 32), " ++ a ++ ");",
      "            mstore((sc_p" ++ i ++ " + 64), " ++ b ++ ");",
      "            let sc_b" ++ i ++ ": memory<bytes> = Typedef.abs(sc_p" ++ i ++ ");",
      set ("sc_b" ++ i)]
  | .nested => [
      "            let sc_size" ++ i ++ ": word = " ++ digit element index ++ ";",
      "            let sc_inner" ++ i ++ ": memory<DynArray<uint256>> = allocateDynamicArray(@uint256, sc_size" ++ i ++ ");",
      "            if (sc_size" ++ i ++ " > 0) {",
      "                IndexAccess.set(sc_inner" ++ i ++ ", uint256(0), uint256(" ++ a ++ "));",
      "            }",
      "            if (sc_size" ++ i ++ " > 1) {",
      "                IndexAccess.set(sc_inner" ++ i ++ ", uint256(1), uint256(" ++ b ++ "));",
      "            }",
      set ("sc_inner" ++ i)]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let element := plan.shape.element
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_", "return_"]
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
  let guarded := (List.range Solcore.Synthesis.Core.ArrayReturn.maxCount).map fun index =>
    ["        if (sc_count > " ++ toString index ++ ") {"] ++ elementLines element index ++ ["        }"]
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++
      "(flags: uint256, input: uint256, choice: uint256, length: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_choice: word = Typedef.rep(choice);",
    "        let sc_count: word = (Typedef.rep(length) % 4);",
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
    "        let sc_rk: word = (sc_result * " ++ multiplierLiteral ++ ");",
    "        let sc_mix: word = ((sload(1) * " ++ multiplierLiteral ++ ") ^ sc_last);",
    "        let sc_items: memory<DynArray<" ++ elementType element ++ ">> = allocateDynamicArray(@" ++
      elementType element ++ ", sc_count);"] ++ guarded.flatten ++
    ["        let sc_encoded: word = Typedef.rep(abi_encode(sc_items));",
    "        return_((sc_encoded + 32), mload(sc_encoded));",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.ArrayReturn
