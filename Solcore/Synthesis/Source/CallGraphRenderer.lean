import Solcore.Synthesis.Source.PrimitiveRenderer

/-! Scalar source rendering with direct calls to earlier named Word helpers.
The primitive formatting and operand snapshots match PrimitiveRenderer. Helper
indices follow the Word-local prefix; neither functions nor host values escape.
This tested printer does not assert source meaning preservation. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallGraphRenderer

open Solcore.Core.Wire
open Solcore.Synthesis.Core (Target)
open ScalarRenderer (Rendered)

def supportedUnary := PrimitiveRenderer.supportedUnary
def supportedBinary := PrimitiveRenderer.supportedBinary
def supportedTernary := PrimitiveRenderer.supportedTernary

/-- Syntax support is separate from the existing checked function boundary. -/
def supported : Expr → Bool
  | .word _ | .bool _ | .var _ => true
  | .letE initializer body => supported initializer && supported body
  | .ifE condition yes no => supported condition && supported yes && supported no
  | .unary operation operand => supportedUnary operation && supported operand
  | .binary operation left right => supportedBinary operation && supported left && supported right
  | .ternary operation first second third =>
      supportedTernary operation && supported first && supported second && supported third
  | .apply (.var _) argument => supported argument
  | _ => false

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"

private def name (index : Nat) : String := "sc_v" ++ toString index

private def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    name nextId, nextId + 1⟩

private def snapshot (indent : Nat) (value : Rendered) : Rendered :=
  let captured := bindValue .word indent value.nextId value.value
  ⟨value.lines ++ captured.lines, captured.value, captured.nextId⟩

private def unaryValue (operation : UnaryOp) (operand : String) : Except EmitError String :=
  match operation with
  | .boolNot => .ok ("(!" ++ operand ++ ")")
  | .wordNot => .ok ("(~" ++ operand ++ ")")
  | .wordClz => .ok ("sc_clz(" ++ operand ++ ")")
  | _ => .error (.unsupportedUnary operation)

private def binaryValue (operation : BinaryOp) (left right : String) : Except EmitError String :=
  let infixValue (token : String) := "(" ++ left ++ " " ++ token ++ " " ++ right ++ ")"
  let call (callee first second : String) := callee ++ "(" ++ first ++ ", " ++ second ++ ")"
  match operation with
  | .wordAdd => .ok (infixValue "+")
  | .wordSub => .ok (infixValue "-")
  | .wordMul => .ok (infixValue "*")
  | .wordAnd => .ok (infixValue "&")
  | .wordOr => .ok (infixValue "|")
  | .wordXor => .ok (infixValue "^")
  | .wordEq => .ok (infixValue "==")
  | .wordGt => .ok (infixValue ">")
  | .wordDiv => .ok (call "sc_div" left right)
  | .wordMod => .ok (call "sc_mod" left right)
  | .wordShl => .ok (call "sc_shl" right left)
  | .wordShr => .ok (call "sc_shr" right left)
  | .wordSar => .ok (call "sc_sar" right left)
  | .wordSdiv => .ok (call "sc_sdiv" left right)
  | .wordSmod => .ok (call "sc_smod" left right)
  | .wordSgt => .ok ("tobool(" ++ call "sc_sgt" left right ++ ")")
  | .wordByte => .ok (call "sc_byte" left right)
  | .wordPow => .ok (call "sc_exp" left right)
  | .wordSignExtend => .ok (call "sc_signextend" left right)
  | _ => .error (.unsupportedBinary operation)

private def ternaryValue (operation : TernaryOp) (first second third : String) : String :=
  let callee := match operation with
    | .wordAddMod => "sc_addmod"
    | .wordMulMod => "sc_mulmod"
  callee ++ "(" ++ first ++ ", " ++ second ++ ", " ++ third ++ ")"

/-- Bindings are nearest first, as in the original Core function. Raw opcode
arguments are captured left to right before reordered shift arguments are
printed. A call snapshots its argument before invoking its named helper.
Branch-local computations remain inside their selected branch. -/
def renderWithFunctions (functions : List String) (target : Target) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok (bindValue .word indent nextId (toString value.val))
  | .bool value => .ok (bindValue .bool indent nextId (if value then "true" else "false"))
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← renderWithFunctions functions .word locals indent nextId initializer
      let binding := bindValue .word indent value.nextId value.value
      let rest ← renderWithFunctions functions target (binding.value :: locals) indent binding.nextId body
      return ⟨value.lines ++ binding.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← renderWithFunctions functions .bool locals indent nextId condition
      let result := bindValue target indent tested.nextId (zero target)
      let selected ← renderWithFunctions functions target locals (indent + 4) result.nextId yes
      let fallback ← renderWithFunctions functions target locals (indent + 4) selected.nextId no
      return ⟨tested.lines ++ result.lines ++
        [line indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
        [line (indent + 4) (result.value ++ " = " ++ selected.value ++ ";"), line indent "} else {"] ++
        fallback.lines ++ [line (indent + 4) (result.value ++ " = " ++ fallback.value ++ ";"), line indent "}"],
        result.value, fallback.nextId⟩
  | .unary operation operand => do
      unless supportedUnary operation do throw (.unsupportedUnary operation)
      let value ← renderWithFunctions functions (if operation == .boolNot then .bool else .word) locals indent nextId operand
      let value := if operation == .wordClz then snapshot indent value else value
      let expression ← unaryValue operation value.value
      let result := bindValue target indent value.nextId expression
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      unless supportedBinary operation do throw (.unsupportedBinary operation)
      let first ← renderWithFunctions functions .word locals indent nextId left
      let first := if Source.supportedBinary operation then first else snapshot indent first
      let second ← renderWithFunctions functions .word locals indent first.nextId right
      let second := if Source.supportedBinary operation then second else snapshot indent second
      let expression ← binaryValue operation first.value second.value
      let result := bindValue target indent second.nextId expression
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .ternary operation first second third => do
      let first := snapshot indent (← renderWithFunctions functions .word locals indent nextId first)
      let second := snapshot indent (← renderWithFunctions functions .word locals indent first.nextId second)
      let third := snapshot indent (← renderWithFunctions functions .word locals indent second.nextId third)
      let result := bindValue target indent third.nextId (ternaryValue operation first.value second.value third.value)
      return ⟨first.lines ++ second.lines ++ third.lines ++ result.lines, result.value, result.nextId⟩
  | .unit => .error (.unsupportedExpression "unit")
  | .integer _ => .error (.unsupportedExpression "integer")
  | .pair _ _ => .error (.unsupportedExpression "pair")
  | .first _ => .error (.unsupportedExpression "first")
  | .second _ => .error (.unsupportedExpression "second")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply (.var index) argument => do
      unless target == .word do throw (.unsupportedExpression "apply")
      if index < locals.length then throw (.unsupportedExpression "apply")
      let some callee := functions[index - locals.length]? |
        throw (.unsupportedExpression "apply")
      let value := snapshot indent (← renderWithFunctions functions .word locals indent nextId argument)
      let result := bindValue .word indent value.nextId (callee ++ "(" ++ value.value ++ ")")
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .apply _ _ => .error (.unsupportedExpression "apply")
  | .inLeft _ _ => .error (.unsupportedExpression "inLeft")
  | .inRight _ _ => .error (.unsupportedExpression "inRight")
  | .caseE _ _ _ => .error (.unsupportedExpression "caseE")
  | .newCell _ _ => .error (.unsupportedExpression "newCell")
  | .loadCell _ => .error (.unsupportedExpression "loadCell")
  | .storeCell _ _ => .error (.unsupportedExpression "storeCell")
  | .construct _ _ => .error (.unsupportedExpression "construct")
  | .matchData _ _ _ _ => .error (.unsupportedExpression "matchData")

end Solcore.Synthesis.Source.CallGraphRenderer
