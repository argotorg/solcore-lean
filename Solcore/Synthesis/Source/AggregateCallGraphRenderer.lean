import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Source.CallGraphRenderer

/-! Source rendering of immutable Word pairs, Word sums, projections and case
payload scopes composed with calls to earlier named Word helpers. Scalar
operations, raw primitive aliases, operand snapshots and calls use exactly the
call-graph formatting; aggregate values use the tuple, sum and match forms of
the aggregate profile. This tested printer does not assert meaning preservation. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AggregateCallGraphRenderer

open Solcore.Core.Wire

/-- Every Core binder is named; helper indices follow this complete context. -/
inductive Binding where
  | word (name : String)
  | bool (name : String)
  | wordPair (name : String)
  | wordSum (name : String)

def Binding.kind : Binding → Solcore.Synthesis.Core.Aggregates.Local
  | .word _ => .word
  | .bool _ => .bool
  | .wordPair _ => .wordPair
  | .wordSum _ => .wordSum

def Binding.name : Binding → String
  | .word name | .bool name | .wordPair name | .wordSum name => name

abbrev Target := Solcore.Synthesis.Core.Aggregates.Target
abbrev Rendered := ScalarRenderer.Rendered

private def scalar? : Target → Option Solcore.Synthesis.Core.Target
  | .word => some .word
  | .bool => some .bool
  | _ => none

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"
  | .wordPair => "(word, word)"
  | .wordSum => "sum<word, word>"
  | .unit => "unit"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"
  | .wordPair => "(0, 0)"
  | .wordSum => "inl(0)"
  | .unit => ""

private def name (index : Nat) : String := "sc_v" ++ toString index

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[CallGraphRenderer.line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    name nextId, nextId + 1⟩

private def binding (target : Target) (value : String) : Option Binding :=
  match target with
  | .word => some (.word value)
  | .bool => some (.bool value)
  | .wordPair => some (.wordPair value)
  | .wordSum => some (.wordSum value)
  | .unit => none

private def kinds (bindings : List Binding) : List Solcore.Synthesis.Core.Aggregates.Local :=
  bindings.map Binding.kind

/-- Bind the selected pair component through a single evaluation of the pair. -/
private def project (left : Bool) (indent : Nat) (rendered : Rendered) : Rendered :=
  let result := bindValue .word indent rendered.nextId "0"
  let first := "sc_p" ++ toString result.nextId
  let second := "sc_p" ++ toString (result.nextId + 1)
  ⟨rendered.lines ++ result.lines ++ [
    CallGraphRenderer.line indent ("match (" ++ rendered.value ++ ") {"),
    CallGraphRenderer.line (indent + 4) ("case (" ++ first ++ ", " ++ second ++ ") {"),
    CallGraphRenderer.line (indent + 8) (result.value ++ " = " ++ (if left then first else second) ++ ";"),
    CallGraphRenderer.line (indent + 4) "}", CallGraphRenderer.line indent "}"],
    result.value, result.nextId + 2⟩

private def inject (constructor : String) (indent : Nat) (rendered : Rendered) : Rendered :=
  let result := bindValue .wordSum indent rendered.nextId (constructor ++ "(" ++ rendered.value ++ ")")
  ⟨rendered.lines ++ result.lines, result.value, result.nextId⟩

/-- Bindings are nearest first, as in the original Core function. Scalar and
call cases follow `CallGraphRenderer.renderWithFunctions` line for line. A
projection or sum scrutinee is evaluated once; only case payloads extend scope.
Branch-local computations remain inside their selected branch. -/
def render (functions : List String) (target : Target) (bindings : List Binding) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok (bindValue .word indent nextId (toString value.val))
  | .bool value => .ok (bindValue .bool indent nextId (if value then "true" else "false"))
  | .var index => match bindings[index]? with
      | some bound =>
          if bound.kind == Solcore.Synthesis.Core.Aggregates.Target.toLocal target then
            .ok ⟨[], bound.name, nextId⟩
          else .error (.unsupportedExpression "local used at a different type")
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let some kind := Solcore.Synthesis.Core.Aggregates.infer? (kinds bindings) functions.length initializer |
        throw (.unsupportedExpression "unsupported local initializer")
      let value ← render functions kind bindings indent nextId initializer
      let bound := bindValue kind indent value.nextId value.value
      let some named := binding kind bound.value | throw (.unsupportedExpression "Unit local")
      let rest ← render functions target (named :: bindings) indent bound.nextId body
      return ⟨value.lines ++ bound.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← render functions .bool bindings indent nextId condition
      let result := bindValue target indent tested.nextId (zero target)
      let selected ← render functions target bindings (indent + 4) result.nextId yes
      let fallback ← render functions target bindings (indent + 4) selected.nextId no
      return ⟨tested.lines ++ result.lines ++
        [CallGraphRenderer.line indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
        [CallGraphRenderer.line (indent + 4) (result.value ++ " = " ++ selected.value ++ ";"),
          CallGraphRenderer.line indent "} else {"] ++ fallback.lines ++
        [CallGraphRenderer.line (indent + 4) (result.value ++ " = " ++ fallback.value ++ ";"),
          CallGraphRenderer.line indent "}"], result.value, fallback.nextId⟩
  | .unary operation operand => do
      let some scalarTarget := scalar? target | throw (.unsupportedExpression "non-scalar unary result")
      unless CallGraphRenderer.supportedUnary operation do throw (.unsupportedUnary operation)
      let value ← render functions (if operation == .boolNot then .bool else .word) bindings indent nextId operand
      let value := if operation == .wordClz then CallGraphRenderer.snapshot indent value else value
      let expression ← CallGraphRenderer.unaryValue operation value.value
      let result := CallGraphRenderer.bindValue scalarTarget indent value.nextId expression
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      let some scalarTarget := scalar? target | throw (.unsupportedExpression "non-scalar binary result")
      unless CallGraphRenderer.supportedBinary operation do throw (.unsupportedBinary operation)
      let first ← render functions .word bindings indent nextId left
      let first := if Source.supportedBinary operation then first else CallGraphRenderer.snapshot indent first
      let second ← render functions .word bindings indent first.nextId right
      let second := if Source.supportedBinary operation then second else CallGraphRenderer.snapshot indent second
      let expression ← CallGraphRenderer.binaryValue operation first.value second.value
      let result := CallGraphRenderer.bindValue scalarTarget indent second.nextId expression
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .ternary operation first second third => do
      unless target == .word do throw (.unsupportedExpression "non-Word ternary result")
      let first := CallGraphRenderer.snapshot indent (← render functions .word bindings indent nextId first)
      let second := CallGraphRenderer.snapshot indent (← render functions .word bindings indent first.nextId second)
      let third := CallGraphRenderer.snapshot indent (← render functions .word bindings indent second.nextId third)
      let result := CallGraphRenderer.bindValue .word indent third.nextId
        (CallGraphRenderer.ternaryValue operation first.value second.value third.value)
      return ⟨first.lines ++ second.lines ++ third.lines ++ result.lines, result.value, result.nextId⟩
  | .apply (.var index) argument => do
      unless target == .word do throw (.unsupportedExpression "apply")
      if index < bindings.length then throw (.unsupportedExpression "apply")
      let some callee := functions[index - bindings.length]? | throw (.unsupportedExpression "apply")
      let value := CallGraphRenderer.snapshot indent (← render functions .word bindings indent nextId argument)
      let result := CallGraphRenderer.bindValue .word indent value.nextId (callee ++ "(" ++ value.value ++ ")")
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .pair left right => do
      unless target == .wordPair do throw (.unsupportedExpression "pair")
      let first ← render functions .word bindings indent nextId left
      let second ← render functions .word bindings indent first.nextId right
      let result := bindValue .wordPair indent second.nextId ("(" ++ first.value ++ ", " ++ second.value ++ ")")
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .first operand => do
      unless target == .word do throw (.unsupportedExpression "projection")
      return project true indent (← render functions .wordPair bindings indent nextId operand)
  | .second operand => do
      unless target == .word do throw (.unsupportedExpression "projection")
      return project false indent (← render functions .wordPair bindings indent nextId operand)
  | .inLeft .word payload => do
      unless target == .wordSum do throw (.unsupportedExpression "inLeft")
      return inject "inl" indent (← render functions .word bindings indent nextId payload)
  | .inRight .word payload => do
      unless target == .wordSum do throw (.unsupportedExpression "inRight")
      return inject "inr" indent (← render functions .word bindings indent nextId payload)
  | .caseE scrutinee left right => do
      let tested ← render functions .wordSum bindings indent nextId scrutinee
      let result := bindValue target indent tested.nextId (zero target)
      let leftPayload := "sc_p" ++ toString result.nextId
      let selected ← render functions target (.word leftPayload :: bindings) (indent + 8) (result.nextId + 1) left
      let rightPayload := "sc_p" ++ toString selected.nextId
      let fallback ← render functions target (.word rightPayload :: bindings) (indent + 8) (selected.nextId + 1) right
      return ⟨tested.lines ++ result.lines ++ [CallGraphRenderer.line indent ("match (" ++ tested.value ++ ") {"),
        CallGraphRenderer.line (indent + 4) ("case inl(" ++ leftPayload ++ ") {")] ++ selected.lines ++
        [CallGraphRenderer.line (indent + 8) (result.value ++ " = " ++ selected.value ++ ";"),
          CallGraphRenderer.line (indent + 4) "}",
          CallGraphRenderer.line (indent + 4) ("case inr(" ++ rightPayload ++ ") {")] ++ fallback.lines ++
        [CallGraphRenderer.line (indent + 8) (result.value ++ " = " ++ fallback.value ++ ";"),
          CallGraphRenderer.line (indent + 4) "}", CallGraphRenderer.line indent "}"],
        result.value, fallback.nextId⟩
  | .unit => .error (.unsupportedExpression "unit")
  | .integer _ => .error (.unsupportedExpression "integer")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply _ _ => .error (.unsupportedExpression "apply")
  | .inLeft _ _ => .error (.unsupportedExpression "inLeft")
  | .inRight _ _ => .error (.unsupportedExpression "inRight")
  | .newCell _ _ => .error (.unsupportedExpression "newCell")
  | .loadCell _ => .error (.unsupportedExpression "loadCell")
  | .storeCell _ _ => .error (.unsupportedExpression "storeCell")
  | .construct _ _ => .error (.unsupportedExpression "construct")
  | .matchData _ _ _ _ => .error (.unsupportedExpression "matchData")

end Solcore.Synthesis.Source.AggregateCallGraphRenderer
