import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Source.CallGraphRenderer

/-! Immutable Word pairs and sums coexist with private mutable Word locals.
Operands are rendered in Core evaluation order. Projection operands and sum
scrutinees are evaluated once; only case payloads extend the Core context.
Scalar operations, including the raw primitive aliases and their operand
snapshots, use exactly the call-graph formatting helpers. -/
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

/-- A rendered scalar operand in the shared call-graph helper representation. -/
private def scalarValue (rendered : Rendered) : Except EmitError ScalarRenderer.Rendered := do
  return ⟨rendered.lines, ← requireValue rendered, rendered.nextId⟩

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
      let result ← scalarTarget target
      unless CallGraphRenderer.supportedUnary operation do throw (.unsupportedUnary operation)
      let operandTarget := if operation == .boolNot then Target.bool else Target.word
      let value ← scalarValue (← render functions operandTarget bindings indent nextId operand)
      let value := if operation == .wordClz then CallGraphRenderer.snapshot indent value else value
      let bound := CallGraphRenderer.bindValue result indent value.nextId
        (← CallGraphRenderer.unaryValue operation value.value)
      return ⟨value.lines ++ bound.lines, some bound.value, bound.nextId⟩
  | .binary operation left right => do
      let result ← scalarTarget target
      unless CallGraphRenderer.supportedBinary operation do throw (.unsupportedBinary operation)
      let first ← scalarValue (← render functions .word bindings indent nextId left)
      let first := if Source.supportedBinary operation then first else CallGraphRenderer.snapshot indent first
      let second ← scalarValue (← render functions .word bindings indent first.nextId right)
      let second := if Source.supportedBinary operation then second else CallGraphRenderer.snapshot indent second
      let bound := CallGraphRenderer.bindValue result indent second.nextId
        (← CallGraphRenderer.binaryValue operation first.value second.value)
      return ⟨first.lines ++ second.lines ++ bound.lines, some bound.value, bound.nextId⟩
  | .ternary operation first second third => do
      unless target == .word do throw (.unsupportedExpression "non-Word ternary result")
      let first := CallGraphRenderer.snapshot indent
        (← scalarValue (← render functions .word bindings indent nextId first))
      let second := CallGraphRenderer.snapshot indent
        (← scalarValue (← render functions .word bindings indent first.nextId second))
      let third := CallGraphRenderer.snapshot indent
        (← scalarValue (← render functions .word bindings indent second.nextId third))
      let bound := CallGraphRenderer.bindValue .word indent third.nextId
        (CallGraphRenderer.ternaryValue operation first.value second.value third.value)
      return ⟨first.lines ++ second.lines ++ third.lines ++ bound.lines, some bound.value, bound.nextId⟩
  | .apply (.var index) argument => do
      if index < bindings.length then throw (.unsupportedExpression "apply")
      let some callee := functions[index - bindings.length]? | throw (.unsupportedExpression "apply")
      let argument ← render functions .word bindings indent nextId argument
      let value ← requireValue argument
      let result := bindValue .word indent argument.nextId (callee ++ "(" ++ value ++ ")")
      return ⟨argument.lines ++ result.lines, result.value, result.nextId⟩
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

/-- The raw opcode aliases of `Primitive.opcodeImport`, in the same order. -/
def opcodeAliases : List String :=
  ["div as sc_div", "mod as sc_mod", "shl as sc_shl", "shr as sc_shr", "sar as sc_sar",
    "sdiv as sc_sdiv", "smod as sc_smod", "sgt as sc_sgt", "addmod as sc_addmod", "mulmod as sc_mulmod",
    "clz as sc_clz", "byte as sc_byte", "exp as sc_exp", "signextend as sc_signextend"]

/-- Whether rendering prints a raw alias: Clz, a binary operation outside the
original scalar set, or any ternary operation. Expressions this renderer
rejects, such as data constructors, never reach an import decision. -/
def usesOpcodeAliases : Expr → Bool
  | .unary operation operand => operation == .wordClz || usesOpcodeAliases operand
  | .binary operation left right =>
      (CallGraphRenderer.supportedBinary operation && !Source.supportedBinary operation) ||
        usesOpcodeAliases left || usesOpcodeAliases right
  | .ternary _ _ _ _ => true
  | .letE first second | .pair first second | .apply first second | .storeCell first second =>
      usesOpcodeAliases first || usesOpcodeAliases second
  | .ifE first second third | .caseE first second third =>
      usesOpcodeAliases first || usesOpcodeAliases second || usesOpcodeAliases third
  | .first operand | .second operand | .inLeft _ operand | .inRight _ operand
  | .newCell _ operand | .loadCell operand | .lambda _ _ operand => usesOpcodeAliases operand
  | .unit | .bool _ | .word _ | .integer _ | .var _ | .construct _ _ | .matchData _ _ _ _ => false

/-- Emitters without another `std.opcodes` import add the alias import only
when a rendered body uses an alias; other programs keep their exact text. -/
def opcodeImports (bodies : List Expr) : List String :=
  if bodies.any usesOpcodeAliases then
    ["import { " ++ ", ".intercalate opcodeAliases ++ " } from std.opcodes;"]
  else []

/-- Emitters with an existing `std.opcodes` import append the aliases to it,
again only when a rendered body uses one. -/
def opcodeImportWith (names : List String) (bodies : List Expr) : String :=
  "import {" ++ ", ".intercalate (names ++ if bodies.any usesOpcodeAliases then opcodeAliases else []) ++
    "} from std.opcodes;"

end Solcore.Synthesis.Source.AggregateRenderer
