import Solcore.Synthesis.Core.Fragment

/-! Deterministic source emission for the initial differential-testing subset.
The input is checker-sealed Core. Source rendering is tested against the pinned
Rust frontend; preservation of source meaning is not a theorem of this module. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source

open Solcore.Core.Wire
open Solcore.Synthesis.Core (CheckedWordProgram Target)

def emitterVersion : String := "solcore-source-g0-v1"
def wrapperVersion : String := "solcore-word-contract-v1"
def contractName : String := "SynthesizedG0"
def methodName : String := "run"
def methodSignature : String := "run()"
def deployPath : List String := ["SynthesizedG0Deploy"]
def runtimePath : List String := ["SynthesizedG0Deploy", "SynthesizedG0"]

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

/-- Syntax support only. Scope and typing are checked by `CheckedWordProgram`. -/
def supported : Expr → Bool
  | .word _ | .bool _ | .var _ => true
  | .letE initializer body => supported initializer && supported body
  | .ifE condition yes no => supported condition && supported yes && supported no
  | .unary operation operand => supportedUnary operation && supported operand
  | .binary operation left right => supportedBinary operation && supported left && supported right
  | _ => false

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

private structure Rendered where
  lines : List String
  value : String
  nextId : Nat

private def bindValue (target : Target) (indent nextId : Nat) (value : String) : Rendered :=
  ⟨[line indent ("let " ++ name nextId ++ ": " ++ typeName target ++ " = " ++ value ++ ";")],
    name nextId, nextId + 1⟩

/-- Locals follow Core's nearest-binder-first indices. Every temporary is
fresh across both branches, and branch computations stay inside their block. -/
private def render (target : Target) (locals : List String) (indent nextId : Nat) :
    Expr → Except EmitError Rendered
  | .word value => .ok (bindValue .word indent nextId (toString value.val))
  | .bool value => .ok (bindValue .bool indent nextId (if value then "true" else "false"))
  | .var index => match locals[index]? with
      | some binding => .ok ⟨[], binding, nextId⟩
      | none => .error (.unboundLocal index)
  | .letE initializer body => do
      let value ← render .word locals indent nextId initializer
      let binding := bindValue .word indent value.nextId value.value
      let rest ← render target (binding.value :: locals) indent binding.nextId body
      return ⟨value.lines ++ binding.lines ++ rest.lines, rest.value, rest.nextId⟩
  | .ifE condition yes no => do
      let tested ← render .bool locals indent nextId condition
      let result := bindValue target indent tested.nextId (zero target)
      let selected ← render target locals (indent + 4) result.nextId yes
      let fallback ← render target locals (indent + 4) selected.nextId no
      return ⟨tested.lines ++ result.lines ++
        [line indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
        [line (indent + 4) (result.value ++ " = " ++ selected.value ++ ";"), line indent "} else {"] ++
        fallback.lines ++ [line (indent + 4) (result.value ++ " = " ++ fallback.value ++ ";"), line indent "}"],
        result.value, fallback.nextId⟩
  | .unary operation operand => do
      let token ← unaryToken operation
      let value ← render (if operation == .boolNot then .bool else .word) locals indent nextId operand
      let result := bindValue target indent value.nextId ("(" ++ token ++ value.value ++ ")")
      return ⟨value.lines ++ result.lines, result.value, result.nextId⟩
  | .binary operation left right => do
      let token ← binaryToken operation
      let first ← render .word locals indent nextId left
      let second ← render .word locals indent first.nextId right
      let result := bindValue target indent second.nextId ("(" ++ first.value ++ " " ++ token ++ " " ++ second.value ++ ")")
      return ⟨first.lines ++ second.lines ++ result.lines, result.value, result.nextId⟩
  | .ternary operation _ _ _ => .error (.unsupportedTernary operation)
  | .unit => .error (.unsupportedExpression "unit")
  | .integer _ => .error (.unsupportedExpression "integer")
  | .pair _ _ => .error (.unsupportedExpression "pair")
  | .first _ => .error (.unsupportedExpression "first")
  | .second _ => .error (.unsupportedExpression "second")
  | .lambda _ _ _ => .error (.unsupportedExpression "lambda")
  | .apply _ _ => .error (.unsupportedExpression "apply")
  | .inLeft _ _ => .error (.unsupportedExpression "inLeft")
  | .inRight _ _ => .error (.unsupportedExpression "inRight")
  | .caseE _ _ _ => .error (.unsupportedExpression "caseE")
  | .newCell _ _ => .error (.unsupportedExpression "newCell")
  | .loadCell _ => .error (.unsupportedExpression "loadCell")
  | .storeCell _ _ => .error (.unsupportedExpression "storeCell")
  | .construct _ _ => .error (.unsupportedExpression "construct")
  | .matchData _ _ _ _ => .error (.unsupportedExpression "matchData")

/-- Emit a single zero-argument ABI method. Its uint256 wrapper exposes the
original Word as exactly 32 return bytes. Unsupported operations are errors,
including operations in a branch that is known to be untaken. -/
def emit (program : CheckedWordProgram) : Except EmitError EmittedProgram := do
  let body ← render .word [] 8 0 program.program.body
  let lines := ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "() public returns (uint256) {"] ++ body.lines ++
    ["        return uint256(" ++ body.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source
