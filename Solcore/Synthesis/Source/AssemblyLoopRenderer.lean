import Solcore.Synthesis.Source.AssemblyRenderer

/-! Inline Yul for scalar call-graph steps: helpers become Yul functions and a
body becomes Yul statements. Expressions render as in the `switch` form of
`AssemblyRenderer.renderYul`, and a call names its helper's Yul function. With
`pairs`, every helper returns its result and its argument, and each call binds
both before its expression uses the first. `renderTail` assigns a function's
`sc_ret` and returns through `leave` after the then branch of every conditional
in tail position. This is a tested printer, not a source meaning-preservation
theorem. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyLoopRenderer

open Solcore.Core.Wire
open ScalarRenderer (Rendered)
open AssemblyRenderer (unaryCall binaryCall ternaryCall)

def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def call (callee : String) (arguments : List String) : String :=
  callee ++ "(" ++ String.intercalate ", " arguments ++ ")"

def yulName (index : Nat) : String := "sc_y" ++ toString index

private def unsupported (name : String) : EmitError := .unsupportedExpression name

/-- Yul statements and the Yul expression of a value. Word locals are nearest
first, and the helpers' Yul function names follow them, also nearest first, as
in the original Core graph. A conditional's branches stay inside their own
blocks, so a call in a branch runs only there. Every operation and helper is
pure, so Yul's argument order cannot be observed. -/
def render (functions : List String) (pairs : Bool) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok ⟨[], toString value.val, nextId⟩
  | .bool value => .ok ⟨[], if value then "1" else "0", nextId⟩
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← render functions pairs locals indent nextId initializer
      let binding := yulName value.nextId
      let rest ← render functions pairs (binding :: locals) indent (value.nextId + 1) body
      return ⟨value.lines ++ [line indent ("let " ++ binding ++ " := " ++ value.value)] ++ rest.lines,
        rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← render functions pairs locals indent nextId condition
      let result := yulName tested.nextId
      let selected ← render functions pairs locals (indent + 4) (tested.nextId + 1) yes
      let fallback ← render functions pairs locals (indent + 4) selected.nextId no
      return ⟨tested.lines ++ [line indent ("let " ++ result ++ " := 0"),
          line indent ("switch " ++ tested.value), line indent "case 0 {"] ++
        fallback.lines ++ [line (indent + 4) (result ++ " := " ++ fallback.value), line indent "}",
          line indent "default {"] ++
        selected.lines ++ [line (indent + 4) (result ++ " := " ++ selected.value), line indent "}"],
        result, fallback.nextId⟩
  | .unary operation operand => do
      let some callee := unaryCall operation | throw (.unsupportedUnary operation)
      let value ← render functions pairs locals indent nextId operand
      return ⟨value.lines, call callee [value.value], value.nextId⟩
  | .binary operation left right => do
      let some (callee, reversed) := binaryCall operation | throw (.unsupportedBinary operation)
      let first ← render functions pairs locals indent nextId left
      let second ← render functions pairs locals indent first.nextId right
      let arguments := if reversed then [second.value, first.value] else [first.value, second.value]
      return ⟨first.lines ++ second.lines, call callee arguments, second.nextId⟩
  | .ternary operation first second third => do
      let first ← render functions pairs locals indent nextId first
      let second ← render functions pairs locals indent first.nextId second
      let third ← render functions pairs locals indent second.nextId third
      return ⟨first.lines ++ second.lines ++ third.lines,
        call (ternaryCall operation) [first.value, second.value, third.value], third.nextId⟩
  | .apply (.var index) argument => do
      if index < locals.length then throw (unsupported "apply")
      let some callee := functions[index - locals.length]? | throw (unsupported "apply")
      let value ← render functions pairs locals indent nextId argument
      if pairs then
        let result := yulName value.nextId
        return ⟨value.lines ++ [line indent ("let " ++ result ++ ", " ++ yulName (value.nextId + 1) ++ " := " ++
          call callee [value.value])], result, value.nextId + 2⟩
      else return ⟨value.lines, call callee [value.value], value.nextId⟩
  | .apply _ _ => .error (unsupported "apply")
  | .unit => .error (unsupported "unit")
  | .integer _ => .error (unsupported "integer")
  | .pair _ _ => .error (unsupported "pair")
  | .first _ => .error (unsupported "first")
  | .second _ => .error (unsupported "second")
  | .lambda _ _ _ => .error (unsupported "lambda")
  | .inLeft _ _ => .error (unsupported "inLeft")
  | .inRight _ _ => .error (unsupported "inRight")
  | .caseE _ _ _ => .error (unsupported "caseE")
  | .newCell _ _ => .error (unsupported "newCell")
  | .loadCell _ => .error (unsupported "loadCell")
  | .storeCell _ _ => .error (unsupported "storeCell")
  | .construct _ _ => .error (unsupported "construct")
  | .matchData _ _ _ _ => .error (unsupported "matchData")

/-- A function body that assigns `sc_ret` on every path. A conditional in tail
position becomes a Yul `if` whose then branch assigns and leaves, followed by
its else branch at the same depth; a `let` keeps its body in tail position.
Returns the statements and the next free temporary. -/
def renderTail (functions : List String) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError (List String × Nat)
  | .letE initializer body => do
      let value ← render functions false locals indent nextId initializer
      let binding := yulName value.nextId
      let (rest, next) ← renderTail functions (binding :: locals) indent (value.nextId + 1) body
      return (value.lines ++ [line indent ("let " ++ binding ++ " := " ++ value.value)] ++ rest, next)
  | .ifE condition yes no => do
      let tested ← render functions false locals indent nextId condition
      let (selected, next) ← renderTail functions locals (indent + 4) tested.nextId yes
      let (fallback, next) ← renderTail functions locals indent next no
      return (tested.lines ++ [line indent ("if " ++ tested.value ++ " {")] ++ selected ++
        [line (indent + 4) "leave", line indent "}"] ++ fallback, next)
  | expression => do
      let value ← render functions false locals indent nextId expression
      return (value.lines ++ [line indent ("sc_ret := " ++ value.value)], value.nextId)

end Solcore.Synthesis.Source.AssemblyLoopRenderer
