import Solcore.Synthesis.Core.MemoryValues
import Solcore.Synthesis.Source.ScalarRenderer

/-! The Solcore source of a memory value plan: std's `memory<bytes>`,
`memory_ref` and `memory<DynArray<uint256>>` values in
`SynthesizedMemoryValues.run(uint256)`, with Word and byte reads through
std's range checks, writes inline or through helpers, and the bounded
`while` forms. The source is a function of the plan; nothing here builds or
reads the Core reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryValues

open Solcore.Synthesis.Core.MemoryValues

def emitterVersion : String := "solcore-source-memory-values-v1"
def wrapperVersion : String := "solcore-word-memory-values-contract-v1"
def contractName : String := "SynthesizedMemoryValues"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def deployPath : List String := ["SynthesizedMemoryValuesDeploy"]
def runtimePath : List String := ["SynthesizedMemoryValuesDeploy", "SynthesizedMemoryValues"]

def refName : Ref → String
  | .bytes number => "sc_b" ++ toString number
  | .slice number => "sc_s" ++ toString number
  | .array number => "sc_a" ++ toString number

/-- The loop's position: `sc_counter`, or `(sc_i + sc_j)` in a nested loop. -/
def positionText : Loop → String
  | .single _ => "sc_counter"
  | .nested .. => "(sc_i + sc_j)"

def operandText (position : String) : Operand → String
  | .input => "sc_x"
  | .add constant => "(sc_x + " ++ toString constant ++ ")"
  | .mul constant => "(sc_x * " ++ toString constant ++ ")"
  | .xor constant => "(sc_x ^ " ++ toString constant ++ ")"
  | .acc => "sc_r"
  | .counter => position

def indexText (position : String) : Index → String
  | .literal value => toString value
  | .input shift modulus => "mod(shr(" ++ toString shift ++ ", sc_x), " ++ toString modulus ++ ")"
  | .counter scale offset =>
      let scaled := if scale = 1 then position else "(" ++ position ++ " * " ++ toString scale ++ ")"
      if offset = 0 then scaled else "(" ++ scaled ++ " + " ++ toString offset ++ ")"

def partText (position : String) : Part → String
  | .word operand => "bytes32(" ++ operandText position operand ++ ")"
  | .zeros count => "empty(" ++ toString count ++ ")"
  | .value ref => refName ref

def buildText (position : String) : Build → String
  | .toBytes part => "to_bytes(" ++ partText position part ++ ")"
  | .concat left right => "concat(" ++ partText position left ++ ", " ++ partText position right ++ ")"

def cutText (source : String) : Cut → String
  | .drop start => "slice_(" ++ source ++ ", " ++ toString start ++ ")"
  | .take kept => "truncate(" ++ source ++ ", " ++ toString kept ++ ")"
  | .window start kept => "truncate(slice_(" ++ source ++ ", " ++ toString start ++ "), " ++ toString kept ++ ")"

def accessText (position value : String) : Access → String
  | .length => "MemorySize.len(" ++ value ++ ")"
  | .word index => "sc_word(" ++ value ++ ", " ++ indexText position index ++ ")"
  | .byte index => "sc_byte(" ++ value ++ ", " ++ indexText position index ++ ")"
  | .hash => "Typedef.rep(keccak256_(" ++ value ++ "))"
  | .element index false => "Typedef.rep(" ++ value ++ "[uint256(" ++ indexText position index ++ ")])"
  | .element index true => "Typedef.rep(IndexAccess.get(" ++ value ++ ", uint256(" ++ indexText position index ++ ")))"

/-- Declaration numbers so far, by kind. -/
structure Names where
  bytes : Nat := 0
  slices : Nat := 0
  arrays : Nat := 0

private def arrayType : String := "memory<DynArray<uint256>>"

/-- An action's lines and the declaration numbers after it. -/
def actionLines (position : String) (names : Names) : Action → List String × Names
  | .bytes build =>
      (["let sc_b" ++ toString names.bytes ++ ": memory<bytes> = " ++ buildText position build ++ ";"],
       {names with bytes := names.bytes + 1})
  | .slice source cut =>
      (["let sc_s" ++ toString names.slices ++ ": memory_ref = " ++ cutText (refName source) cut ++ ";"],
       {names with slices := names.slices + 1})
  | .alias source =>
      match source with
      | .array _ =>
          (["let sc_a" ++ toString names.arrays ++ ": " ++ arrayType ++ " = " ++ refName source ++ ";"],
           {names with arrays := names.arrays + 1})
      | _ =>
          (["let sc_b" ++ toString names.bytes ++ ": memory<bytes> = " ++ refName source ++ ";"],
           {names with bytes := names.bytes + 1})
  | .array allocated elements =>
      let name := "sc_a" ++ toString names.arrays
      let lines := if allocated then
          ("let " ++ name ++ ": " ++ arrayType ++ " = allocateDynamicArray(@uint256, " ++ toString elements.length ++ ");") ::
          elements.zipIdx.map fun (element, index) =>
            "IndexAccess.set(" ++ name ++ ", uint256(" ++ toString index ++ "), uint256(" ++ operandText position element ++ "));"
        else
          ["let " ++ name ++ ": " ++ arrayType ++ " = [" ++
            ", ".intercalate (elements.map fun element => "uint256(" ++ operandText position element ++ ")") ++ "];"]
      (lines, {names with arrays := names.arrays + 1})
  | .write target index value width form =>
      let target := refName target |> fun name => (name, target.isArray)
      let index := indexText position index
      let value := operandText position value
      let line := match target.2, width, form with
        | true, _, .inline => "IndexAccess.set(" ++ target.1 ++ ", uint256(" ++ index ++ "), uint256(" ++ value ++ "));"
        | true, _, .helper => "sc_aput(" ++ target.1 ++ ", " ++ index ++ ", " ++ value ++ ");"
        | false, .word, .inline => "mstore(MemoryPointer.ptr(truncate(slice_(" ++ target.1 ++ ", " ++ index ++ "), 32)), " ++ value ++ ");"
        | false, .byte, .inline => "mstore8(MemoryPointer.ptr(truncate(slice_(" ++ target.1 ++ ", " ++ index ++ "), 1)), " ++ value ++ ");"
        | false, .word, .helper => "sc_put(" ++ target.1 ++ ", " ++ index ++ ", " ++ value ++ ");"
        | false, .byte, .helper => "sc_put8(" ++ target.1 ++ ", " ++ index ++ ", " ++ value ++ ");"
      ([line], names)
  | .observe fold constant value access =>
      let operator := match fold with
        | .add => " + "
        | .xor => " ^ "
      (["sc_r = ((sc_r * " ++ toString constant ++ ")" ++ operator ++ accessText position (refName value) access ++ ");"], names)

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def bodyLines (position : String) (names : Names) (actions : List Action) : List String × Names :=
  actions.foldl (fun (lines, names) action =>
    let (more, names) := actionLines position names action
    (lines ++ more, names)) ([], names)

def loopLines (names : Names) (loop : Loop) (body : List Action) : List String × Names :=
  let position := positionText loop
  let (inner, names) := bodyLines position names body
  match loop with
  | .single mask =>
      (["let sc_limit: word = (sc_x & " ++ toString mask ++ ");",
        "let sc_counter: word = 0;",
        "while (sc_limit > sc_counter) {"] ++ indent 4 inner ++
       ["    sc_counter = (sc_counter + 1);", "}"], names)
  | .nested outer bound innerMask =>
      let innerBound := match bound with
        | .input => "(sc_x & " ++ toString innerMask ++ ")"
        | .counter => "((sc_i + 1) & " ++ toString innerMask ++ ")"
      (["let sc_outer: word = (sc_x & " ++ toString outer ++ ");",
        "let sc_i: word = 0;",
        "let sc_inner: word = 0;",
        "let sc_j: word = 0;",
        "while (sc_outer > sc_i) {",
        "    sc_inner = " ++ innerBound ++ ";",
        "    sc_j = 0;",
        "    while (sc_inner > sc_j) {"] ++ indent 8 inner ++
       ["        sc_j = (sc_j + 1);", "    }", "    sc_i = (sc_i + 1);", "}"], names)

/-- The helpers in emission order, each emitted when an action needs it. -/
def helperNames : List String := ["sc_word", "sc_byte", "sc_put", "sc_put8", "sc_aput"]

def actionHelpers : Action → List String
  | .observe _ _ _ (.word _) => ["sc_word"]
  | .observe _ _ _ (.byte _) => ["sc_byte"]
  | .write target _ _ width .helper =>
      if target.isArray then ["sc_aput"] else match width with
        | .word => ["sc_put"]
        | .byte => ["sc_put8"]
  | _ => []

def planHelpers (plan : Plan) : List String :=
  let used := plan.steps.flatMap fun step => step.actions.flatMap actionHelpers
  helperNames.filter used.contains

def helperLines : String → List String
  | "sc_word" => [
      "function sc_word<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
      "    return mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)));", "}", ""]
  | "sc_byte" => [
      "function sc_byte<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
      "    return shr(248, mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1))));", "}", ""]
  | "sc_put" => [
      "function sc_put<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
      "    mstore(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)), sc_w);", "}", ""]
  | "sc_put8" => [
      "function sc_put8<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
      "    mstore8(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1)), sc_w);", "}", ""]
  | "sc_aput" => [
      "function sc_aput(sc_a: memory<DynArray<uint256>>, sc_i: word, sc_w: word) returns (()) {",
      "    IndexAccess.set(sc_a, uint256(sc_i), uint256(sc_w));", "}", ""]
  | _ => []

def emit (plan : Plan) : EmittedProgram := Id.run do
  let mut names : Names := {}
  let mut lines : List String := []
  for step in plan.steps do
    match step with
    | .action action =>
        let (more, next) := actionLines "sc_counter" names action
        lines := lines ++ more
        names := next
    | .loop loop body =>
        let (more, next) := loopLines names loop body
        lines := lines ++ more
        names := next
  let source := ["import * from std;", "import * from std.dispatch;",
      "import { mload, mstore, mstore8, shr, mod } from std.opcodes;", ""] ++
    (planHelpers plan).flatMap helperLines ++
    ["contract " ++ contractName ++ " {",
     "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
     "        let sc_x: word = Typedef.rep(input);",
     "        let sc_r: word = 0;"] ++ indent 8 lines ++
    ["        return uint256(sc_r);", "    }", "}"]
  return {
    source := String.intercalate "\n" source ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.MemoryValues
