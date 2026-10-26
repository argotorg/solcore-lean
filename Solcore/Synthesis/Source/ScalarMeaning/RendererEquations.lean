import Solcore.Core.Primitive
import Solcore.Synthesis.Source.ScalarRenderer
import Solcore.Synthesis.Source.ScalarMeaning.Print
import Solcore.Synthesis.Source.ScalarMeaning.Semantics

/-! Equations for the actual `ScalarRenderer.render`, stated with the scalar
source syntax and printer. They unfold the real implementation; nothing here
re-implements it. The second half relates the Word operations used by Core to
the independent EVM operations of the source semantics. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)

/-- The renderer's temporary names `sc_v0`, `sc_v1`, ... -/
def temporary (index : Nat) : String := "sc_v" ++ toString index

theorem temporary_injective {first second : Nat}
    (same : temporary first = temporary second) : first = second := by
  have chars := congrArg String.toList same
  simp only [temporary, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr,
    List.append_cancel_left_eq] at chars
  have values := congrArg (fun digits => Nat.ofDigitChars 10 digits 0) chars
  simpa using values

theorem temporary_inj {first second : Nat} :
    temporary first = temporary second ↔ first = second :=
  ⟨temporary_injective, fun same => same ▸ rfl⟩

def LocalType.ofTarget : Target → LocalType
  | .word => .word
  | .bool => .bool

/-- The initial value printed for an `if` result. -/
def zeroExpr : Target → Expr
  | .word => .number 0
  | .bool => .bool false

/-- The renderer's spelling of `zeroExpr`. -/
def zeroText : Target → String
  | .word => "0"
  | .bool => "false"

/-- Source operator selected for a Core unary operation, if printable. -/
def sourceUnary? : Solcore.Core.Wire.UnaryOp → Option UnaryOp
  | .boolNot => some .not
  | .wordNot => some .bitNot
  | _ => none

/-- Source operator selected for a Core binary operation, if printable. -/
def sourceBinary? : Solcore.Core.Wire.BinaryOp → Option BinaryOp
  | .wordAdd => some .add
  | .wordSub => some .sub
  | .wordMul => some .mul
  | .wordAnd => some .bitAnd
  | .wordOr => some .bitOr
  | .wordXor => some .bitXor
  | .wordEq => some .eq
  | .wordGt => some .gt
  | _ => none

namespace RendererEquations

theorem word (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (value : Solcore.Core.Word) :
    ScalarRenderer.renderWithFunctions functions target locals indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        temporary first, first + 1⟩ := by
  simp only [ScalarRenderer.renderWithFunctions]
  rfl

theorem bool (functions : List String) (target : Target) (locals : List String) (indent first : Nat) (value : Bool) :
    ScalarRenderer.renderWithFunctions functions target locals indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        temporary first, first + 1⟩ := by
  simp only [ScalarRenderer.renderWithFunctions]
  rfl

theorem var (functions : List String) (target : Target) (locals : List String) (indent first index : Nat) :
    ScalarRenderer.renderWithFunctions functions target locals indent first (.var index) =
      match locals[index]? with
      | some binding => .ok ⟨[], binding, first⟩
      | none => .error (.unboundLocal index) := by
  simp only [ScalarRenderer.renderWithFunctions]
  cases locals[index]? <;> rfl

theorem letE (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (initializer body : Solcore.Core.Wire.Expr) :
    ScalarRenderer.renderWithFunctions functions target locals indent first (.letE initializer body) =
      (ScalarRenderer.renderWithFunctions functions .word locals indent first initializer).bind fun value =>
        (ScalarRenderer.renderWithFunctions functions target (temporary value.nextId :: locals) indent (value.nextId + 1)
          body).bind
          fun rest =>
            .ok ⟨value.lines ++
                Stmt.lines indent (.letDecl (temporary value.nextId) .word (.name value.value)) ++
                rest.lines,
              rest.value, rest.nextId⟩ := by
  simp only [ScalarRenderer.renderWithFunctions]
  rfl

/-- The `if` result is declared with its zero value, then assigned at the end
of each branch block. -/
theorem ifE (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (condition yes no : Solcore.Core.Wire.Expr) :
    ScalarRenderer.renderWithFunctions functions target locals indent first (.ifE condition yes no) =
      (ScalarRenderer.renderWithFunctions functions .bool locals indent first condition).bind fun tested =>
        (ScalarRenderer.renderWithFunctions functions target locals (indent + 4) (tested.nextId + 1) yes).bind fun selected =>
          (ScalarRenderer.renderWithFunctions functions target locals (indent + 4) selected.nextId no).bind fun fallback =>
            .ok ⟨tested.lines ++
                [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
                  (LocalType.ofTarget target).spelling ++ " = " ++ zeroText target ++ ";")] ++
                [indentLine indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
                [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ selected.value ++ ";"),
                  indentLine indent "} else {"] ++
                fallback.lines ++
                [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ fallback.value ++ ";"),
                  indentLine indent "}"],
              temporary tested.nextId, fallback.nextId⟩ := by
  simp only [ScalarRenderer.renderWithFunctions]
  cases target <;> rfl

theorem unary (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.UnaryOp) (operand : Solcore.Core.Wire.Expr) :
    ScalarRenderer.renderWithFunctions functions target locals indent first (.unary op operand) =
      match sourceUnary? op with
      | some sourceOp =>
          (ScalarRenderer.renderWithFunctions functions (if op == .boolNot then .bool else .word) locals indent first
            operand).bind
            fun value =>
              .ok ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId)
                  (LocalType.ofTarget target) (.unary sourceOp (.name value.value))),
                temporary value.nextId, value.nextId + 1⟩
      | none => .error (.unsupportedUnary op) := by
  simp only [ScalarRenderer.renderWithFunctions]
  cases op <;> cases target <;> rfl

theorem binary (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (left right : Solcore.Core.Wire.Expr) :
    ScalarRenderer.renderWithFunctions functions target locals indent first (.binary op left right) =
      match sourceBinary? op with
      | some sourceOp =>
          (ScalarRenderer.renderWithFunctions functions .word locals indent first left).bind fun leftValue =>
            (ScalarRenderer.renderWithFunctions functions .word locals indent leftValue.nextId right).bind fun rightValue =>
              .ok ⟨leftValue.lines ++ rightValue.lines ++
                  Stmt.lines indent (.letDecl (temporary rightValue.nextId)
                    (LocalType.ofTarget target)
                    (.binary sourceOp (.name leftValue.value) (.name rightValue.value))),
                temporary rightValue.nextId, rightValue.nextId + 1⟩
      | none => .error (.unsupportedBinary op) := by
  simp only [ScalarRenderer.renderWithFunctions]
  cases op <;> cases target <;> rfl

/-- A direct call to an earlier helper: the argument is rendered first and the
call result is bound to a fresh `word` temporary. -/
theorem apply (functions : List String) (target : Target) (locals : List String)
    (indent first index : Nat) (argument : Solcore.Core.Wire.Expr) :
    ScalarRenderer.renderWithFunctions functions target locals indent first
        (.apply (.var index) argument) =
      if functions.isEmpty || index < locals.length then .error (.unsupportedExpression "apply")
      else
        match functions[index - locals.length]? with
        | none => .error (.unsupportedExpression "apply")
        | some callee =>
            (ScalarRenderer.renderWithFunctions functions .word locals indent first
              argument).bind fun value =>
              .ok ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId) .word
                  (.call1 callee (.name value.value))),
                temporary value.nextId, value.nextId + 1⟩ := by
  simp only [ScalarRenderer.renderWithFunctions]
  by_cases rejected : (functions.isEmpty || decide (index < locals.length)) = true
  · simp only [rejected, if_true]
    rfl
  · simp only [Bool.not_eq_true] at rejected
    simp only [rejected, Bool.false_eq_true, if_false]
    cases functions[index - locals.length]? <;> rfl

end RendererEquations

end Solcore.Synthesis.Source.ScalarMeaning
