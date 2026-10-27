import Solcore.Synthesis.Source.PrimitiveRenderer

/-! Inline Yul for the checked scalar Word functions of the primitive profile.
`renderYul` prints a whole body as Yul statements inside one `assembly` block;
`renderOperations` keeps Solcore lets, conditionals, literals and `!` and puts
every other operation in its own `assembly` block assigning a fresh Solcore
Word local. Comparisons give Yul's Words 0 and 1, which correspond to Core's
Bools. This is a tested printer, not a source meaning-preservation theorem. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyRenderer

open Solcore.Core.Wire
open Solcore.Synthesis.Core (Target FeatureMask)
open ScalarRenderer (Rendered)

/-- How a function's Solcore and Yul parts mix. -/
inductive Form where
  /-- The whole body in Yul, each Core `if` as a `switch`. -/
  | switch
  /-- The whole body in Yul, each Core `if` as two Yul `if`s. -/
  | branches
  /-- Solcore control flow, each operation in its own `assembly` block. -/
  | operations
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Form

def all : List Form := [.switch, .branches, .operations]

def name : Form → String
  | .switch => "switch"
  | .branches => "if"
  | .operations => "operations"

def ofString? : String → Option Form
  | "switch" => some .switch
  | "if" => some .branches
  | "operations" => some .operations
  | _ => none

end Form

/-- The G0 features both renderers render: every operator and form. -/
def support : FeatureMask := PrimitiveRenderer.support

/-- The Yul builtin of a unary operation. -/
def unaryCall : UnaryOp → Option String
  | .boolNot => some "iszero"
  | .wordNot => some "not"
  | .wordClz => some "clz"
  | _ => none

/-- The Yul builtin of a binary operation, and whether it takes its Core operands
in reverse: Yul shifts take the shift amount first. -/
def binaryCall : BinaryOp → Option (String × Bool)
  | .wordAdd => some ("add", false)
  | .wordSub => some ("sub", false)
  | .wordMul => some ("mul", false)
  | .wordDiv => some ("div", false)
  | .wordMod => some ("mod", false)
  | .wordAnd => some ("and", false)
  | .wordOr => some ("or", false)
  | .wordXor => some ("xor", false)
  | .wordEq => some ("eq", false)
  | .wordGt => some ("gt", false)
  | .wordSgt => some ("sgt", false)
  | .wordShl => some ("shl", true)
  | .wordShr => some ("shr", true)
  | .wordSar => some ("sar", true)
  | .wordByte => some ("byte", false)
  | .wordPow => some ("exp", false)
  | .wordSignExtend => some ("signextend", false)
  | .wordSdiv => some ("sdiv", false)
  | .wordSmod => some ("smod", false)
  | _ => none

def ternaryCall : TernaryOp → String
  | .wordAddMod => "addmod"
  | .wordMulMod => "mulmod"

/-- Comparisons, whose Core results are Bools. -/
def comparison : BinaryOp → Bool
  | .wordEq | .wordGt | .wordSgt => true
  | _ => false

private def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def call (callee : String) (arguments : List String) : String :=
  callee ++ "(" ++ String.intercalate ", " arguments ++ ")"

private def yulName (index : Nat) : String := "sc_y" ++ toString index

private def unsupported (name : String) : EmitError := .unsupportedExpression name

/-- Yul statements and the Yul expression of a value. Bindings are nearest
first, as in the original Core function. A conditional's branches stay inside
their own blocks; an operation nests its operands' expressions after their
statements. Every operation is pure, so Yul's argument order cannot be
observed. -/
def renderYul (branches : Bool) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok ⟨[], toString value.val, nextId⟩
  | .bool value => .ok ⟨[], if value then "1" else "0", nextId⟩
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← renderYul branches locals indent nextId initializer
      let binding := yulName value.nextId
      let rest ← renderYul branches (binding :: locals) indent (value.nextId + 1) body
      return ⟨value.lines ++ [line indent ("let " ++ binding ++ " := " ++ value.value)] ++ rest.lines,
        rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← renderYul branches locals indent nextId condition
      if branches then
        let held := yulName tested.nextId
        let result := yulName (tested.nextId + 1)
        let selected ← renderYul branches locals (indent + 4) (tested.nextId + 2) yes
        let fallback ← renderYul branches locals (indent + 4) selected.nextId no
        return ⟨tested.lines ++ [line indent ("let " ++ held ++ " := " ++ tested.value),
            line indent ("let " ++ result ++ " := 0"), line indent ("if " ++ held ++ " {")] ++
          selected.lines ++ [line (indent + 4) (result ++ " := " ++ selected.value), line indent "}",
            line indent ("if iszero(" ++ held ++ ") {")] ++
          fallback.lines ++ [line (indent + 4) (result ++ " := " ++ fallback.value), line indent "}"],
          result, fallback.nextId⟩
      else
        let result := yulName tested.nextId
        let selected ← renderYul branches locals (indent + 4) (tested.nextId + 1) yes
        let fallback ← renderYul branches locals (indent + 4) selected.nextId no
        return ⟨tested.lines ++ [line indent ("let " ++ result ++ " := 0"),
            line indent ("switch " ++ tested.value), line indent "case 0 {"] ++
          fallback.lines ++ [line (indent + 4) (result ++ " := " ++ fallback.value), line indent "}",
            line indent "default {"] ++
          selected.lines ++ [line (indent + 4) (result ++ " := " ++ selected.value), line indent "}"],
          result, fallback.nextId⟩
  | .unary operation operand => do
      let some callee := unaryCall operation | throw (.unsupportedUnary operation)
      let value ← renderYul branches locals indent nextId operand
      return ⟨value.lines, call callee [value.value], value.nextId⟩
  | .binary operation left right => do
      let some (callee, reversed) := binaryCall operation | throw (.unsupportedBinary operation)
      let first ← renderYul branches locals indent nextId left
      let second ← renderYul branches locals indent first.nextId right
      let arguments := if reversed then [second.value, first.value] else [first.value, second.value]
      return ⟨first.lines ++ second.lines, call callee arguments, second.nextId⟩
  | .ternary operation first second third => do
      let first ← renderYul branches locals indent nextId first
      let second ← renderYul branches locals indent first.nextId second
      let third ← renderYul branches locals indent second.nextId third
      return ⟨first.lines ++ second.lines ++ third.lines,
        call (ternaryCall operation) [first.value, second.value, third.value], third.nextId⟩
  | .unit => .error (unsupported "unit")
  | .integer _ => .error (unsupported "integer")
  | .pair _ _ => .error (unsupported "pair")
  | .first _ => .error (unsupported "first")
  | .second _ => .error (unsupported "second")
  | .lambda _ _ _ => .error (unsupported "lambda")
  | .apply _ _ => .error (unsupported "apply")
  | .inLeft _ _ => .error (unsupported "inLeft")
  | .inRight _ _ => .error (unsupported "inRight")
  | .caseE _ _ _ => .error (unsupported "caseE")
  | .newCell _ _ => .error (unsupported "newCell")
  | .loadCell _ => .error (unsupported "loadCell")
  | .storeCell _ _ => .error (unsupported "storeCell")
  | .construct _ _ => .error (unsupported "construct")
  | .matchData _ _ _ _ => .error (unsupported "matchData")

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"

private def name (index : Nat) : String := "sc_v" ++ toString index

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    name nextId, nextId + 1⟩

/-- A fresh Solcore Word local that one `assembly` block assigns. -/
private def assemble (indent nextId : Nat) (expression : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": word = 0;"), line indent "assembly {",
    line (indent + 4) (name nextId ++ " := " ++ expression), line indent "}"], name nextId, nextId + 1⟩

/-- Solcore lets, conditionals, literals and `!` as in the primitive renderer;
every other operation reads Solcore Word locals in its own `assembly` block. A
comparison's Word becomes a Bool through std's `tobool`. -/
def renderOperations (target : Target) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok (bindValue .word indent nextId (toString value.val))
  | .bool value => .ok (bindValue .bool indent nextId (if value then "true" else "false"))
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← renderOperations .word locals indent nextId initializer
      let binding := bindValue .word indent value.nextId value.value
      let rest ← renderOperations target (binding.value :: locals) indent binding.nextId body
      return ⟨value.lines ++ binding.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← renderOperations .bool locals indent nextId condition
      let result := bindValue target indent tested.nextId (zero target)
      let selected ← renderOperations target locals (indent + 4) result.nextId yes
      let fallback ← renderOperations target locals (indent + 4) selected.nextId no
      return ⟨tested.lines ++ result.lines ++
        [line indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
        [line (indent + 4) (result.value ++ " = " ++ selected.value ++ ";"), line indent "} else {"] ++
        fallback.lines ++ [line (indent + 4) (result.value ++ " = " ++ fallback.value ++ ";"), line indent "}"],
        result.value, fallback.nextId⟩
  | .unary .boolNot operand => do
      let value ← renderOperations .bool locals indent nextId operand
      let result := bindValue .bool indent value.nextId ("(!" ++ value.value ++ ")")
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .unary operation operand => do
      let some callee := unaryCall operation | throw (.unsupportedUnary operation)
      let value ← renderOperations .word locals indent nextId operand
      let result := assemble indent value.nextId (call callee [value.value])
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      let some (callee, reversed) := binaryCall operation | throw (.unsupportedBinary operation)
      let first ← renderOperations .word locals indent nextId left
      let second ← renderOperations .word locals indent first.nextId right
      let arguments := if reversed then [second.value, first.value] else [first.value, second.value]
      let word := assemble indent second.nextId (call callee arguments)
      if comparison operation then
        let result := bindValue .bool indent word.nextId ("tobool(" ++ word.value ++ ")")
        return ⟨first.lines ++ second.lines ++ word.lines ++ result.lines, result.value, result.nextId⟩
      else
        return ⟨first.lines ++ second.lines ++ word.lines, word.value, word.nextId⟩
  | .ternary operation first second third => do
      let first ← renderOperations .word locals indent nextId first
      let second ← renderOperations .word locals indent first.nextId second
      let third ← renderOperations .word locals indent second.nextId third
      let result := assemble indent third.nextId
        (call (ternaryCall operation) [first.value, second.value, third.value])
      return ⟨first.lines ++ second.lines ++ third.lines ++ result.lines, result.value, result.nextId⟩
  | .unit => .error (unsupported "unit")
  | .integer _ => .error (unsupported "integer")
  | .pair _ _ => .error (unsupported "pair")
  | .first _ => .error (unsupported "first")
  | .second _ => .error (unsupported "second")
  | .lambda _ _ _ => .error (unsupported "lambda")
  | .apply _ _ => .error (unsupported "apply")
  | .inLeft _ _ => .error (unsupported "inLeft")
  | .inRight _ _ => .error (unsupported "inRight")
  | .caseE _ _ _ => .error (unsupported "caseE")
  | .newCell _ _ => .error (unsupported "newCell")
  | .loadCell _ => .error (unsupported "loadCell")
  | .storeCell _ _ => .error (unsupported "storeCell")
  | .construct _ _ => .error (unsupported "construct")
  | .matchData _ _ _ _ => .error (unsupported "matchData")

end Solcore.Synthesis.Source.AssemblyRenderer
