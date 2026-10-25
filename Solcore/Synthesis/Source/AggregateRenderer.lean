import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Source.ScalarRenderer

/-! Immutable Word pairs and sums coexist with private mutable Word locals.
Operands are rendered in Core evaluation order. Projection operands and sum
scrutinees are evaluated once; only case payloads extend the Core context. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AggregateRenderer

open Solcore.Core.Wire
open Solcore.Synthesis.Core.Aggregates (Target Local)

inductive Binding where
  | word (name : String)
  | bool (name : String)
  | cellWord (name : String)
  | unit
  | wordPair (name : String)
  | wordSum (name : String)

def Binding.kind : Binding → Local
  | .word _ => .word
  | .bool _ => .bool
  | .cellWord _ => .cellWord
  | .unit => .unit
  | .wordPair _ => .wordPair
  | .wordSum _ => .wordSum

private def bindingFor (target : Target) (name : String) : Binding :=
  match target with
  | .word => .word name
  | .bool => .bool name
  | .unit => .unit
  | .wordPair => .wordPair name
  | .wordSum => .wordSum name

structure Rendered where
  lines : List String
  value : Option String
  nextId : Nat

private def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def name (index : Nat) : String := "sc_v" ++ toString index
private def cellName (index : Nat) : String := "sc_c" ++ toString index

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"
  | .unit => "unit"
  | .wordPair => "(word, word)"
  | .wordSum => "sum<word, word>"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"
  | .unit => ""
  | .wordPair => "(0, 0)"
  | .wordSum => "inl(0)"

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    some (name nextId), nextId + 1⟩

def requireValue (rendered : Rendered) : Except EmitError String :=
  match rendered.value with
  | some value => .ok value
  | none => .error (.unsupportedExpression "Unit used as a scalar value")

private def scalarTarget : Target → Except EmitError Solcore.Synthesis.Core.Target
  | .word => .ok .word
  | .bool => .ok .bool
  | _ => .error (.unsupportedExpression "non-scalar primitive target")

private def fromScalar (rendered : ScalarRenderer.Rendered) : Rendered :=
  ⟨rendered.lines, some rendered.value, rendered.nextId⟩

private def scalar (target : Target) (operands : List String)
    (indent nextId : Nat) (expression : Expr) : Except EmitError Rendered := do
  return fromScalar (← ScalarRenderer.render (← scalarTarget target) operands indent nextId expression)

private def cell (bindings : List Binding) (index : Nat) : Except EmitError String :=
  match bindings[index]? with
  | some (.cellWord name) => .ok name
  | _ => .error (.unsupportedExpression "cell reference is not a direct private local")

/-- The context includes every Core binder, including elided Unit values.
Helper function indices begin immediately after this complete local context. -/
def render (functions : List String) (target : Target) (bindings : List Binding)
    (indent nextId : Nat) : Expr → Except EmitError Rendered
  | .word value => scalar .word [] indent nextId (.word value)
  | .bool value => scalar .bool [] indent nextId (.bool value)
  | .unit => .ok ⟨[], none, nextId⟩
  | .var index => match bindings[index]? with
      | some (.word value) | some (.bool value)
      | some (.wordPair value) | some (.wordSum value) => .ok ⟨[], some value, nextId⟩
      | some .unit => .ok ⟨[], none, nextId⟩
      | _ => .error (.unboundLocal index)
  | .letE (.newCell .word initializer) body => do
      let initial ← render functions .word bindings indent nextId initializer
      let value ← requireValue initial
      let binding := cellName initial.nextId
      let rest ← render functions target (.cellWord binding :: bindings) indent (initial.nextId + 1) body
      return ⟨initial.lines ++ [line indent ("let " ++ binding ++ ": word = " ++ value ++ ";")] ++ rest.lines,
        rest.value, rest.nextId⟩
  | .letE initializer body => do
      let some kind := Solcore.Synthesis.Core.Aggregates.infer?
          (bindings.map Binding.kind) functions.length initializer |
        throw (.unsupportedExpression "unsupported local initializer")
      let initial ← render functions kind bindings indent nextId initializer
      match kind with
      | .unit =>
        let rest ← render functions target (.unit :: bindings) indent initial.nextId body
        return ⟨initial.lines ++ rest.lines, rest.value, rest.nextId⟩
      | .word | .bool | .wordPair | .wordSum =>
        let value ← requireValue initial
        let bound := bindValue kind indent initial.nextId value
        let binding := bindingFor kind (name initial.nextId)
        let rest ← render functions target (binding :: bindings) indent bound.nextId body
        return ⟨initial.lines ++ bound.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← render functions .bool bindings indent nextId condition
      let conditionValue ← requireValue tested
      if target == .unit then
        let selected ← render functions .unit bindings (indent + 4) tested.nextId yes
        let fallback ← render functions .unit bindings (indent + 4) selected.nextId no
        return ⟨tested.lines ++ [line indent ("if (" ++ conditionValue ++ ") {")] ++
          selected.lines ++ [line indent "} else {"] ++ fallback.lines ++ [line indent "}"],
          none, fallback.nextId⟩
      else
        let result := bindValue target indent tested.nextId (zero target)
        let resultValue ← requireValue result
        let selected ← render functions target bindings (indent + 4) result.nextId yes
        let selectedValue ← requireValue selected
        let fallback ← render functions target bindings (indent + 4) selected.nextId no
        let fallbackValue ← requireValue fallback
        return ⟨tested.lines ++ result.lines ++ [line indent ("if (" ++ conditionValue ++ ") {")] ++
          selected.lines ++ [line (indent + 4) (resultValue ++ " = " ++ selectedValue ++ ";"),
            line indent "} else {"] ++ fallback.lines ++
          [line (indent + 4) (resultValue ++ " = " ++ fallbackValue ++ ";"), line indent "}"],
          some resultValue, fallback.nextId⟩
  | .pair left right => do
      let first ← render functions .word bindings indent nextId left
      let firstValue ← requireValue first
      let second ← render functions .word bindings indent first.nextId right
      let secondValue ← requireValue second
      let result := bindValue .wordPair indent second.nextId
        ("(" ++ firstValue ++ ", " ++ secondValue ++ ")")
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .first operand => do
      let rendered ← render functions .wordPair bindings indent nextId operand
      let value ← requireValue rendered
      let result := bindValue .word indent rendered.nextId "0"
      let resultValue ← requireValue result
      let left := "sc_p" ++ toString result.nextId
      let right := "sc_p" ++ toString (result.nextId + 1)
      return ⟨rendered.lines ++ result.lines ++ [
        line indent ("match (" ++ value ++ ") {"),
        line (indent + 4) ("case (" ++ left ++ ", " ++ right ++ ") {"),
        line (indent + 8) (resultValue ++ " = " ++ left ++ ";"),
        line (indent + 4) "}", line indent "}"],
        result.value, result.nextId + 2⟩
  | .second operand => do
      let rendered ← render functions .wordPair bindings indent nextId operand
      let value ← requireValue rendered
      let result := bindValue .word indent rendered.nextId "0"
      let resultValue ← requireValue result
      let left := "sc_p" ++ toString result.nextId
      let right := "sc_p" ++ toString (result.nextId + 1)
      return ⟨rendered.lines ++ result.lines ++ [
        line indent ("match (" ++ value ++ ") {"),
        line (indent + 4) ("case (" ++ left ++ ", " ++ right ++ ") {"),
        line (indent + 8) (resultValue ++ " = " ++ right ++ ";"),
        line (indent + 4) "}", line indent "}"],
        result.value, result.nextId + 2⟩
  | .inLeft .word payload => do
      let rendered ← render functions .word bindings indent nextId payload
      let value ← requireValue rendered
      let result := bindValue .wordSum indent rendered.nextId ("inl(" ++ value ++ ")")
      return ⟨rendered.lines ++ result.lines, result.value, result.nextId⟩
  | .inRight .word payload => do
      let rendered ← render functions .word bindings indent nextId payload
      let value ← requireValue rendered
      let result := bindValue .wordSum indent rendered.nextId ("inr(" ++ value ++ ")")
      return ⟨rendered.lines ++ result.lines, result.value, result.nextId⟩
  | .caseE scrutinee yes no => do
      let tested ← render functions .wordSum bindings indent nextId scrutinee
      let value ← requireValue tested
      let result := if target == .unit then Rendered.mk [] none tested.nextId
        else bindValue target indent tested.nextId (zero target)
      let leftPayload := "sc_p" ++ toString result.nextId
      let selected ← render functions target (.word leftPayload :: bindings)
        (indent + 8) (result.nextId + 1) yes
      let rightPayload := "sc_p" ++ toString selected.nextId
      let fallback ← render functions target (.word rightPayload :: bindings)
        (indent + 8) (selected.nextId + 1) no
      let selectedLines ← match result.value with
        | none => pure selected.lines
        | some resultValue => do
          let selectedValue ← requireValue selected
          pure (selected.lines ++ [line (indent + 8) (resultValue ++ " = " ++ selectedValue ++ ";")])
      let fallbackLines ← match result.value with
        | none => pure fallback.lines
        | some resultValue => do
          let fallbackValue ← requireValue fallback
          pure (fallback.lines ++ [line (indent + 8) (resultValue ++ " = " ++ fallbackValue ++ ";")])
      return ⟨tested.lines ++ result.lines ++ [line indent ("match (" ++ value ++ ") {"),
        line (indent + 4) ("case inl(" ++ leftPayload ++ ") {")] ++ selectedLines ++
        [line (indent + 4) "}", line (indent + 4) ("case inr(" ++ rightPayload ++ ") {")] ++
        fallbackLines ++ [line (indent + 4) "}", line indent "}"], result.value, fallback.nextId⟩
  | .loadCell (.var index) => do
      return bindValue .word indent nextId (← cell bindings index)
  | .storeCell (.var index) value => do
      let reference ← cell bindings index
      let written ← render functions .word bindings indent nextId value
      let result ← requireValue written
      return ⟨written.lines ++ [line indent (reference ++ " = " ++ result ++ ";")], none, written.nextId⟩
  | .unary operation operand => do
      let operandTarget := if operation == .boolNot then Target.bool else Target.word
      let rendered ← render functions operandTarget bindings indent nextId operand
      let value ← requireValue rendered
      let result ← scalar target [value] indent rendered.nextId (.unary operation (.var 0))
      return ⟨rendered.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      let first ← render functions .word bindings indent nextId left
      let firstValue ← requireValue first
      let second ← render functions .word bindings indent first.nextId right
      let secondValue ← requireValue second
      let result ← scalar target [firstValue, secondValue] indent second.nextId
        (.binary operation (.var 0) (.var 1))
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .apply (.var index) argument => do
      if index < bindings.length then throw (.unsupportedExpression "apply")
      let some callee := functions[index - bindings.length]? | throw (.unsupportedExpression "apply")
      let argument ← render functions .word bindings indent nextId argument
      let value ← requireValue argument
      let result := bindValue .word indent argument.nextId (callee ++ "(" ++ value ++ ")")
      return ⟨argument.lines ++ result.lines, result.value, result.nextId⟩
  | .ternary operation _ _ _ => .error (.unsupportedTernary operation)
  | .integer _ => .error (.unsupportedExpression "integer")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply _ _ => .error (.unsupportedExpression "apply")
  | .inLeft _ _ => .error (.unsupportedExpression "inLeft")
  | .inRight _ _ => .error (.unsupportedExpression "inRight")
  | .newCell _ _ => .error (.unsupportedExpression "newCell outside direct Word let initializer")
  | .loadCell _ => .error (.unsupportedExpression "loadCell")
  | .storeCell _ _ => .error (.unsupportedExpression "storeCell")
  | .construct _ _ => .error (.unsupportedExpression "construct")
  | .matchData _ _ _ _ => .error (.unsupportedExpression "matchData")

end Solcore.Synthesis.Source.AggregateRenderer
