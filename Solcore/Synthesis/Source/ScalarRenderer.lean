import Solcore.Synthesis.Core.FeatureMask

/-! Shared scalar statements for source synthesis. The renderer is a formatting
component; checked profiles supply the scope and type boundary. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source

open Solcore.Core.Wire
open Solcore.Synthesis.Core (Target FeatureMask)

inductive EmitError where
  | unsupportedUnary (operation : UnaryOp)
  | unsupportedBinary (operation : BinaryOp)
  | unsupportedTernary (operation : TernaryOp)
  | unsupportedExpression (constructor : String)
  | unboundLocal (index : Nat)
  deriving Repr, BEq, DecidableEq

structure EmittedProgram where
  source : String
  contractName : String
  methodName : String
  methodSignature : String
  deployPath : List String
  runtimePath : List String
  deriving Repr, BEq, DecidableEq

def supportedUnary : UnaryOp → Bool
  | .boolNot | .wordNot => true
  | _ => false

def supportedBinary : BinaryOp → Bool
  | .wordAdd | .wordSub | .wordMul | .wordAnd | .wordOr | .wordXor | .wordEq | .wordGt => true
  | _ => false

/-- Syntax support only. Scope and typing are supplied by the checked profile. -/
def supported : Expr → Bool
  | .word _ | .bool _ | .var _ => true
  | .letE initializer body => supported initializer && supported body
  | .ifE condition yes no => supported condition && supported yes && supported no
  | .unary operation operand => supportedUnary operation && supported operand
  | .binary operation left right => supportedBinary operation && supported left && supported right
  | _ => false

/-- The G0 features this renderer renders: the scalar operators of
`supportedUnary` and `supportedBinary`, `let` and `if`, and no ternary. -/
def scalarSupport : FeatureMask :=
  FeatureMask.supporting supportedUnary supportedBinary fun _ => false

namespace ScalarRenderer

private def unaryToken : UnaryOp → Except EmitError String
  | .boolNot => .ok "!"
  | .wordNot => .ok "~"
  | operation => .error (.unsupportedUnary operation)

private def binaryToken : BinaryOp → Except EmitError String
  | .wordAdd => .ok "+"
  | .wordSub => .ok "-"
  | .wordMul => .ok "*"
  | .wordAnd => .ok "&"
  | .wordOr => .ok "|"
  | .wordXor => .ok "^"
  | .wordEq => .ok "=="
  | .wordGt => .ok ">"
  | operation => .error (.unsupportedBinary operation)

private def typeName : Target → String
  | .word => "word"
  | .bool => "bool"

private def zero : Target → String
  | .word => "0"
  | .bool => "false"

private def name (index : Nat) : String := "sc_v" ++ toString index
private def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

structure Rendered where
  lines : List String
  value : String
  nextId : Nat

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    name nextId, nextId + 1⟩

/-- Locals follow Core's nearest-binder-first indices. Every temporary is
fresh across both branches, and branch computations stay inside their block.
The function environment is nearest first, after all Word locals. Callee lookup
is allowed only at a direct application, and arguments are evaluated first. -/
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
      let token ← unaryToken operation
      let value ← renderWithFunctions functions (if operation == .boolNot then .bool else .word) locals indent nextId operand
      let result := bindValue target indent value.nextId ("(" ++ token ++ value.value ++ ")")
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      let token ← binaryToken operation
      let first ← renderWithFunctions functions .word locals indent nextId left
      let second ← renderWithFunctions functions .word locals indent first.nextId right
      let result := bindValue target indent second.nextId ("(" ++ first.value ++ " " ++ token ++ " " ++ second.value ++ ")")
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .ternary operation _ _ _ => .error (.unsupportedTernary operation)
  | .unit => .error (.unsupportedExpression "unit")
  | .integer _ => .error (.unsupportedExpression "integer")
  | .pair _ _ => .error (.unsupportedExpression "pair")
  | .first _ => .error (.unsupportedExpression "first")
  | .second _ => .error (.unsupportedExpression "second")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply (.var index) argument => do
      if functions.isEmpty || index < locals.length then
        throw (.unsupportedExpression "apply")
      let some callee := functions[index - locals.length]? |
        throw (.unsupportedExpression "apply")
      let value ← renderWithFunctions functions .word locals indent nextId argument
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


/-- Preserve the original scalar-only renderer and its unsupported-call errors. -/
def render (target : Target) (locals : List String) (indent nextId : Nat)
    (expression : Expr) : Except EmitError Rendered :=
  renderWithFunctions [] target locals indent nextId expression

end ScalarRenderer

end Solcore.Synthesis.Source
