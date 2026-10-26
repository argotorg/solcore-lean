import Solcore.Synthesis.Source.CallGraphRenderer
import Solcore.Synthesis.Source.ScalarMeaning.PrimitiveEquations
import Solcore.Synthesis.Source.ScalarMeaning.Renderer

/-! Equations for the actual `CallGraphRenderer.renderWithFunctions`, stated with
the scalar source syntax and printer. It prints raw opcode calls as the
primitive renderer does, and copies the argument of a helper call into a fresh
`word` temporary before the call. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.ScalarRenderer (Rendered)
open Solcore.Synthesis.Source.CallGraphRenderer (renderWithFunctions)

namespace CallGraphEquations

theorem word (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (value : Solcore.Core.Word) :
    renderWithFunctions functions target locals indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        temporary first, first + 1⟩ := by
  simp only [CallGraphRenderer.renderWithFunctions]
  rfl

theorem bool (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat) (value : Bool) :
    renderWithFunctions functions target locals indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        temporary first, first + 1⟩ := by
  simp only [CallGraphRenderer.renderWithFunctions]
  rfl

theorem var (functions : List String) (target : Target) (locals : List String)
    (indent first index : Nat) :
    renderWithFunctions functions target locals indent first (.var index) =
      match locals[index]? with
      | some binding => .ok ⟨[], binding, first⟩
      | none => .error (.unboundLocal index) := by
  simp only [CallGraphRenderer.renderWithFunctions]
  cases locals[index]? <;> rfl

theorem letE (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (initializer body : Solcore.Core.Wire.Expr) :
    renderWithFunctions functions target locals indent first (.letE initializer body) =
      (renderWithFunctions functions .word locals indent first initializer).bind fun value =>
        (renderWithFunctions functions target (temporary value.nextId :: locals) indent
          (value.nextId + 1) body).bind fun rest =>
            .ok ⟨value.lines ++
                Stmt.lines indent (.letDecl (temporary value.nextId) .word (.name value.value)) ++
                rest.lines,
              rest.value, rest.nextId⟩ := by
  simp only [CallGraphRenderer.renderWithFunctions]
  rfl

theorem ifE (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (condition yes no : Solcore.Core.Wire.Expr) :
    renderWithFunctions functions target locals indent first (.ifE condition yes no) =
      (renderWithFunctions functions .bool locals indent first condition).bind fun tested =>
        (renderWithFunctions functions target locals (indent + 4) (tested.nextId + 1) yes).bind
          fun selected =>
            (renderWithFunctions functions target locals (indent + 4) selected.nextId no).bind
              fun fallback =>
                .ok ⟨tested.lines ++
                    [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
                      (LocalType.ofTarget target).spelling ++ " = " ++ zeroText target ++ ";")] ++
                    [indentLine indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
                    [indentLine (indent + 4)
                        (temporary tested.nextId ++ " = " ++ selected.value ++ ";"),
                      indentLine indent "} else {"] ++
                    fallback.lines ++
                    [indentLine (indent + 4)
                        (temporary tested.nextId ++ " = " ++ fallback.value ++ ";"),
                      indentLine indent "}"],
                  temporary tested.nextId, fallback.nextId⟩ := by
  simp only [CallGraphRenderer.renderWithFunctions]
  cases target <;> rfl

theorem unary (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.UnaryOp) (sourceOp : UnaryOp) (operand : Solcore.Core.Wire.Expr)
    (selected : sourceUnary? op = some sourceOp) :
    renderWithFunctions functions target locals indent first (.unary op operand) =
      (renderWithFunctions functions (if op == .boolNot then .bool else .word) locals indent first
        operand).bind fun value =>
          .ok ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId)
              (LocalType.ofTarget target) (.unary sourceOp (.name value.value))),
            temporary value.nextId, value.nextId + 1⟩ := by
  cases op <;> simp only [sourceUnary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> simp only [CallGraphRenderer.renderWithFunctions] <;> cases target <;> rfl

/-- `CLZ` snapshots its operand, then calls the raw opcode alias. -/
theorem clz (functions : List String) (target : Target) (locals : List String) (indent first : Nat)
    (operand : Solcore.Core.Wire.Expr) :
    renderWithFunctions functions target locals indent first (.unary .wordClz operand) =
      (renderWithFunctions functions .word locals indent first operand).bind fun value =>
        .ok (resultOf indent target (snapshotOf indent value).lines (value.nextId + 1)
          (.call1 "sc_clz" (.name (temporary value.nextId)))) := by
  simp only [CallGraphRenderer.renderWithFunctions]
  cases target <;> rfl

theorem unary_unsupported (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.UnaryOp) (operand : Solcore.Core.Wire.Expr)
    (unsupported : CallGraphRenderer.supportedUnary op = false) :
    renderWithFunctions functions target locals indent first (.unary op operand) =
      .error (.unsupportedUnary op) := by
  cases op <;> simp only [CallGraphRenderer.supportedUnary, PrimitiveRenderer.supportedUnary,
    Source.supportedUnary,
    Bool.true_eq_false] at unsupported <;> rfl

theorem binary (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (sourceOp : BinaryOp) (left right : Solcore.Core.Wire.Expr)
    (selected : sourceBinary? op = some sourceOp) :
    renderWithFunctions functions target locals indent first (.binary op left right) =
      (renderWithFunctions functions .word locals indent first left).bind fun leftValue =>
        (renderWithFunctions functions .word locals indent leftValue.nextId right).bind
          fun rightValue =>
            .ok ⟨leftValue.lines ++ rightValue.lines ++
                Stmt.lines indent (.letDecl (temporary rightValue.nextId)
                  (LocalType.ofTarget target)
                  (.binary sourceOp (.name leftValue.value) (.name rightValue.value))),
              temporary rightValue.nextId, rightValue.nextId + 1⟩ := by
  cases op <;> simp only [sourceBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> simp only [CallGraphRenderer.renderWithFunctions] <;> cases target <;> rfl

/-- Extended binary operations snapshot both operands, left to right, then
call the raw opcode alias. -/
theorem binary_primitive (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (build : String → String → Expr)
    (left right : Solcore.Core.Wire.Expr) (selected : primitiveBinary? op = some build) :
    renderWithFunctions functions target locals indent first (.binary op left right) =
      (renderWithFunctions functions .word locals indent first left).bind fun leftValue =>
        (renderWithFunctions functions .word locals indent (leftValue.nextId + 1) right).bind
          fun rightValue =>
            .ok (resultOf indent target
              ((snapshotOf indent leftValue).lines ++ (snapshotOf indent rightValue).lines)
              (rightValue.nextId + 1)
              (build (temporary leftValue.nextId) (temporary rightValue.nextId))) := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> simp only [CallGraphRenderer.renderWithFunctions] <;> cases target <;> rfl

theorem binary_unsupported (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.BinaryOp) (left right : Solcore.Core.Wire.Expr)
    (unsupported : CallGraphRenderer.supportedBinary op = false) :
    renderWithFunctions functions target locals indent first (.binary op left right) =
      .error (.unsupportedBinary op) := by
  cases op <;> simp only [CallGraphRenderer.supportedBinary, PrimitiveRenderer.supportedBinary,
    Source.supportedBinary,
    Bool.true_eq_false] at unsupported <;> rfl

/-- `ADDMOD` and `MULMOD` snapshot all three operands, then call the raw
opcode alias. -/
theorem ternary (functions : List String) (target : Target) (locals : List String)
    (indent first : Nat)
    (op : Solcore.Core.Wire.TernaryOp) (one two three : Solcore.Core.Wire.Expr) :
    renderWithFunctions functions target locals indent first (.ternary op one two three) =
      (renderWithFunctions functions .word locals indent first one).bind fun oneValue =>
        (renderWithFunctions functions .word locals indent (oneValue.nextId + 1) two).bind
          fun twoValue =>
            (renderWithFunctions functions .word locals indent (twoValue.nextId + 1) three).bind
              fun threeValue =>
                .ok (resultOf indent target
                  ((snapshotOf indent oneValue).lines ++ (snapshotOf indent twoValue).lines ++
                    (snapshotOf indent threeValue).lines)
                  (threeValue.nextId + 1)
                  (.call3 (ternaryCallee op) (.name (temporary oneValue.nextId))
                    (.name (temporary twoValue.nextId))
                    (.name (temporary threeValue.nextId)))) := by
  simp only [CallGraphRenderer.renderWithFunctions]
  cases op <;> cases target <;> rfl

/-- A call to an earlier helper snapshots its argument, then calls the helper. -/
theorem apply_ok {functions : List String} {target : Target} {locals : List String}
    {indent first index : Nat} {argument : Solcore.Core.Wire.Expr} {rendered : Rendered}
    (equation : renderWithFunctions functions target locals indent first
      (.apply (.var index) argument) = .ok rendered) :
    target = .word ∧ locals.length ≤ index ∧ ∃ callee value,
      functions[index - locals.length]? = some callee ∧
      renderWithFunctions functions .word locals indent first argument =
        .ok value ∧
      rendered = resultOf indent .word (snapshotOf indent value).lines (value.nextId + 1)
        (.call1 callee (.name (temporary value.nextId))) := by
  cases target with
  | bool => cases equation
  | word =>
      by_cases below : index < locals.length
      · dsimp only [CallGraphRenderer.renderWithFunctions] at equation
        rw [if_pos below] at equation
        cases equation
      · cases found : functions[index - locals.length]? with
        | none =>
            dsimp only [CallGraphRenderer.renderWithFunctions] at equation
            rw [if_neg below, found] at equation
            cases equation
        | some callee =>
            dsimp only [CallGraphRenderer.renderWithFunctions] at equation
            rw [if_neg below, found] at equation
            obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
            exact ⟨rfl, Nat.le_of_not_lt below, callee, value, rfl, valueEquation,
              (Except.ok.inj equation).symm⟩

end CallGraphEquations
end Solcore.Synthesis.Source.ScalarMeaning
