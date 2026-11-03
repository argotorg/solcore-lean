import Solcore.Synthesis.Core.Integers
import Solcore.Synthesis.Source.ScalarRenderer

/-! The Solcore source of an integer plan: the helpers `sc_h<k>` and
`sc_apply` of a `runtime-checked-arithmetic` plan, then
`SynthesizedCheckedArithmetic.run` or `SynthesizedShifts.run(uint256)`, which
converts the input Word to its inputs and amounts, runs the steps, a block's
variables declared before it, and folds every result into the returned Word.
The source is a function of the plan; nothing here builds or reads the Core
reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Integers

open Solcore.Synthesis.Core.Integers

def arithmeticEmitterVersion : String := "solcore-source-checked-arithmetic-v1"
def arithmeticWrapperVersion : String := "solcore-checked-arithmetic-contract-v1"
def arithmeticContract : String := "SynthesizedCheckedArithmetic"
def shiftEmitterVersion : String := "solcore-source-shifts-v1"
def shiftWrapperVersion : String := "solcore-word-shifts-contract-v1"
def shiftContract : String := "SynthesizedShifts"

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def hexText (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

/-- A literal of the plan's type, a negative one in parentheses. -/
def intText (value : Int) : String := if value < 0 then "(" ++ toString value ++ ")" else toString value

def convertText (type : IntType) (word : String) : String :=
  if type.bytes = 32 then word
  else if type.signed then "sc_signextend(" ++ toString (type.bytes - 1) ++ ", " ++ word ++ ")"
  else "(" ++ word ++ " & " ++ hexText (2 ^ type.bits - 1) ++ ")"

def offsetText (offset : Nat) : String := if offset = 0 then "sc_x" else "(sc_x + " ++ toString offset ++ ")"

/-- `let sc_a<i>: T = …;` or `let sc_k<j>: A = …;`: a Word as itself, an
integer type through `Typedef.abs` of the converted Word. -/
def declaration (name : String) (type : ValueType) (offset : Nat) : String :=
  match type with
  | .word => "let " ++ name ++ ": word = " ++ offsetText offset ++ ";"
  | .int integer =>
      "let " ++ name ++ ": " ++ integer.name ++ " = Typedef.abs(" ++ convertText integer (offsetText offset) ++ ");"

def opSymbol : Op → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"

def testText : Test → String
  | .lt constant => "(sc_x < " ++ toString constant ++ ")"
  | .gt constant => "(sc_x > " ++ toString constant ++ ")"
  | .eq constant => "(sc_x == " ++ toString constant ++ ")"
  | .bits mask value => "((sc_x & " ++ toString mask ++ ") == " ++ toString value ++ ")"

def varName (index : Nat) : String := "sc_v" ++ toString index

def defaultLiteral (index : Nat) : String := toString (IntType.uint256.literals.getD index 0)

def shiftSymbol : Direction → String
  | .left => "<<"
  | .right => ">>"

def operandText (plan : Plan) : Operand → String
  | .input index => "sc_a" ++ toString index
  | .var index => varName index
  | .literal index => intText (plan.type.literals.getD index 0)

def amountText : Amount → String
  | .input index => "sc_k" ++ toString index
  | .literal index => toString (amountLiterals.getD index 0)

/-- The lambda applied by `sc_apply`, its body in a block when `unchecked`. -/
def lambdaLines (plan : Plan) (target : String) (op : Op) (unchecked : Bool) (left right : Operand) : List String :=
  let name := plan.value.name
  let result := "return (sc_l " ++ opSymbol op ++ " " ++ operandText plan right ++ ");"
  [target ++ "sc_apply(lam (sc_l: " ++ name ++ ") -> " ++ name ++ " {"] ++
    indent 4 (if unchecked then ["unchecked {", "    " ++ result, "}"] else [result]) ++
    ["}, " ++ operandText plan left ++ ");"]

/-- A step's statements once its variable is declared, or its declaration in
a checked group: `target` is `let sc_v<n>: T = ` or `sc_v<n> = `. -/
def stepLines (plan : Plan) (vars defaults : Nat) (declared : Bool) : Step → List String
  | .assign form =>
      let name := varName vars
      let target := if declared then name ++ " = " else "let " ++ name ++ ": " ++ plan.value.name ++ " = "
      match form with
      | .binary op left right =>
          [target ++ "(" ++ operandText plan left ++ " " ++ opSymbol op ++ " " ++ operandText plan right ++ ");"]
      | .neg operand => [target ++ "(-" ++ operandText plan operand ++ ");"]
      | .compound op left right =>
          [target ++ operandText plan left ++ ";", name ++ " " ++ opSymbol op ++ "= " ++ operandText plan right ++ ";"]
      | .call helper left right =>
          [target ++ "sc_h" ++ toString helper ++ "(" ++ operandText plan left ++ ", " ++ operandText plan right ++ ");"]
      | .apply op unchecked left right => lambdaLines plan target op unchecked left right
  | .default made =>
      let result := "(sc_d" ++ toString defaults ++ " " ++ opSymbol made.op ++ " " ++ defaultLiteral made.operand ++ ")"
      if declared then ["sc_e" ++ toString defaults ++ " = " ++ result ++ ";"]
      else ["let sc_e" ++ toString defaults ++ " = " ++ result ++ ";"]
  | .shift shift =>
      let name := varName vars
      let target := if declared then name ++ " = " else "let " ++ name ++ ": " ++ plan.value.name ++ " = "
      if shift.compound then
        [target ++ operandText plan shift.value ++ ";",
          name ++ " " ++ shiftSymbol shift.direction ++ "= " ++ amountText shift.amount ++ ";"]
      else [target ++ "(" ++ operandText plan shift.value ++ " " ++ shiftSymbol shift.direction ++ " " ++
        amountText shift.amount ++ ");"]

/-- A defaulted literal's choice, always before any block. -/
def choiceLines (defaults : Nat) (made : Default) : List String :=
  let name := "sc_d" ++ toString defaults
  ["let " ++ name ++ " = " ++ defaultLiteral made.initial ++ ";", "if " ++ testText made.test ++ " {",
    "    " ++ name ++ " = " ++ defaultLiteral made.chosen ++ ";", "}"]

/-- The statements of the groups, with the counts of variables and defaulted
results before each step. -/
def groupLines (plan : Plan) : List String := Id.run do
  let mut lines : List String := []
  let mut vars := 0
  let mut defaults := 0
  for group in plan.groups do
    let mut before : List String := []
    let mut inside : List String := []
    for step in group.steps do
      match step with
      | .default made =>
          before := before ++ choiceLines defaults made
          if group.unchecked then before := before ++ ["let sc_e" ++ toString defaults ++ " = 0;"]
          inside := inside ++ stepLines plan vars defaults group.unchecked step
          defaults := defaults + 1
      | _ =>
          if group.unchecked then before := before ++ ["let " ++ varName vars ++ ": " ++ plan.value.name ++ " = 0;"]
          inside := inside ++ stepLines plan vars defaults group.unchecked step
          vars := vars + 1
    if group.unchecked then lines := lines ++ before ++ ["unchecked {"] ++ indent 4 inside ++ ["}"]
    else lines := lines ++ before ++ inside
  return lines

/-- Every result in creation order, as a Word. -/
def resultWords (plan : Plan) : List String := Id.run do
  let mut words : List String := []
  let mut vars := 0
  let mut defaults := 0
  for (_, step) in plan.steps do
    match step with
    | .default _ =>
        words := words ++ ["Typedef.rep(sc_e" ++ toString defaults ++ ")"]
        defaults := defaults + 1
    | _ =>
        words := words ++ [match plan.value with
          | .word => varName vars
          | .int _ => "Typedef.rep(" ++ varName vars ++ ")"]
        vars := vars + 1
  return words

def unchecked (plan : Plan) : Bool :=
  plan.groups.any (·.unchecked) || plan.helpers.any (·.unchecked) ||
    plan.steps.any fun (_, step) => step matches .assign (.apply _ true _ _)

def applies (plan : Plan) : Bool := plan.steps.any fun (_, step) => step matches .assign (.apply ..)

def imports (plan : Plan) : List String :=
  let signed := plan.type.signed
  ["import * from std;", "import * from std.unsigned;"] ++
    (if signed then ["import * from std.signed;"] else []) ++
    (if unchecked plan then [if signed then "import * from std.unchecked.signed;" else
      "import * from std.unchecked.unsigned;"] else []) ++
    ["import * from std.dispatch;"] ++
    (if signed && plan.type.bytes < 32 then ["import { signextend as sc_signextend } from std.opcodes;"] else [])

def helperLines (plan : Plan) : List String :=
  let name := plan.value.name
  let helpers := plan.helpers.zipIdx.flatMap fun (helper, index) =>
    let result := "return (sc_p " ++ opSymbol helper.op ++ " sc_q);"
    ["function sc_h" ++ toString index ++ "(sc_p: " ++ name ++ ", sc_q: " ++ name ++ ") returns (" ++ name ++ ") {"] ++
      indent 4 (if helper.unchecked then ["unchecked {", "    " ++ result, "}"] else [result]) ++ ["}", ""]
  helpers ++ (if applies plan then
    ["function sc_apply(sc_f: function (" ++ name ++ ") returns (" ++ name ++ "), sc_v: " ++ name ++ ") returns (" ++
      name ++ ") {", "    return sc_f(sc_v);", "}", ""] else [])

def parameterType (plan : Plan) : String := if plan.abi then plan.value.name else "uint256"

def signature (plan : Plan) : String := "run(" ++ parameterType plan ++ ")"

def emitWith (contract : String) (plan : Plan) : EmittedProgram :=
  let name := plan.value.name
  let inputs := plan.inputs.zipIdx.map fun (offset, index) =>
    if plan.abi && index = 0 then "let sc_a0: " ++ name ++ " = input;"
    else declaration ("sc_a" ++ toString index) plan.value offset
  let amounts := plan.amounts.zipIdx.map fun (amount, index) =>
    declaration ("sc_k" ++ toString index) amount.type amount.offset
  let fold := (resultWords plan).map fun word => "sc_acc = ((sc_acc * 1099511628211) ^ " ++ word ++ ");"
  let result := if plan.raw then name else "uint256"
  let body := ["let sc_x: word = Typedef.rep(input);"] ++ inputs ++ amounts ++ ["let sc_acc: word = 0;"] ++
    groupLines plan ++ fold ++ [if plan.raw then "return Typedef.abs(sc_acc);" else "return uint256(sc_acc);"]
  let lines := imports plan ++ [""] ++ helperLines plan ++ ["contract " ++ contract ++ " {",
    "    function run(input: " ++ parameterType plan ++ ") public returns (" ++ result ++ ") {"] ++
    indent 8 body ++ ["    }", "}"]
  { source := String.intercalate "\n" lines ++ "\n", contractName := contract, methodName := "run",
    methodSignature := signature plan, deployPath := [contract ++ "Deploy"],
    runtimePath := [contract ++ "Deploy", contract] }

def emitArithmetic (plan : Plan) : EmittedProgram := emitWith arithmeticContract plan

def emitShifts (plan : Plan) : EmittedProgram := emitWith shiftContract plan

end Solcore.Synthesis.Source.Integers
