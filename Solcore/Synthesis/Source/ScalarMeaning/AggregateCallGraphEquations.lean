import Solcore.Synthesis.Source.AggregateCallGraphRenderer
import Solcore.Synthesis.Source.ScalarMeaning.AggregateControl

/-! Equations for the actual `AggregateCallGraphRenderer.render`, stated with
the source syntax and printer. This renderer prints the aggregate forms of
`AggregateRenderer` and the call-graph formatting of scalar operations and
calls, but has no cells and no Unit values; every binding is a Word, Boolean,
pair or sum. Its private helpers are unfolded by definitional equality. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

abbrev GBinding := AggregateCallGraphRenderer.Binding

/-- A binding of the aggregate call-graph renderer as a binding of the
aggregate renderer; both name the same kinds of value. -/
def GBinding.toAggregate : GBinding → AggregateRenderer.Binding
  | .word name => .word name
  | .bool name => .bool name
  | .wordPair name => .wordPair name
  | .wordSum name => .wordSum name

theorem GBinding.toAggregate_kind (binding : GBinding) :
    binding.toAggregate.kind = binding.kind := by
  cases binding <;> rfl

theorem kinds_toAggregate (bindings : List GBinding) :
    (bindings.map GBinding.toAggregate).map AggregateRenderer.Binding.kind =
      bindings.map AggregateCallGraphRenderer.Binding.kind := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih => simp [GBinding.toAggregate_kind, ih]

/-- The binding the renderer's private `binding` builds for a value kind. -/
def gvalueBinding : ATarget → String → GBinding
  | .bool, name => .bool name
  | .wordPair, name => .wordPair name
  | .wordSum, name => .wordSum name
  | _, name => .word name

theorem gvalueBinding_toAggregate {kind : ATarget} (valued : kind ≠ .unit) (name : String) :
    (gvalueBinding kind name).toAggregate = valueBinding kind name := by
  cases kind
  case unit => exact absurd rfl valued
  all_goals rfl

namespace AggregateCallGraphEquations

variable {functions : List String} {target : ATarget} {bindings : List GBinding}
  {indent first : Nat} {rendered : ScalarRenderer.Rendered}

theorem word (value : Solcore.Core.Word) :
    AggregateCallGraphRenderer.render functions target bindings indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        temporary first, first + 1⟩ := by
  simp only [AggregateCallGraphRenderer.render]
  rfl

theorem bool (value : Bool) :
    AggregateCallGraphRenderer.render functions target bindings indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        temporary first, first + 1⟩ := by
  simp only [AggregateCallGraphRenderer.render]
  rfl

theorem var_ok {index : Nat}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.var index) = .ok rendered) :
    ∃ name, target ≠ .unit ∧ bindings[index]? = some (gvalueBinding target name) ∧
      rendered = ⟨[], name, first⟩ := by
  simp only [AggregateCallGraphRenderer.render] at equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      cases binding <;> cases target <;> first
        | exact ⟨_, by simp, rfl, (Except.ok.inj equation).symm⟩
        | cases equation

theorem letE_ok {initializer body : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ kind value rest, kind ≠ .unit ∧
      infer? (bindings.map AggregateCallGraphRenderer.Binding.kind) functions.length initializer =
        some kind ∧
      AggregateCallGraphRenderer.render functions kind bindings indent first initializer =
        .ok value ∧
      AggregateCallGraphRenderer.render functions target
        (gvalueBinding kind (temporary value.nextId) :: bindings) indent (value.nextId + 1)
          body = .ok rest ∧
      rendered = ⟨value.lines ++
        Stmt.lines indent (.letDecl (temporary value.nextId) (ATarget.localType kind)
          (.name value.value)) ++
        rest.lines, rest.value, rest.nextId⟩ := by
  simp only [AggregateCallGraphRenderer.render] at equation
  split at equation
  · rename_i kind inferred
    obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
    cases kind
    case unit => cases equation
    all_goals
      obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
      exact ⟨_, value, rest, by simp, inferred, valueEquation, restEquation,
        (Except.ok.inj equation).symm⟩
  · cases equation

theorem ifE_ok {condition yes no : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested selected fallback,
      AggregateCallGraphRenderer.render functions .bool bindings indent first condition =
        .ok tested ∧
      AggregateCallGraphRenderer.render functions target bindings (indent + 4)
        (tested.nextId + 1) yes = .ok selected ∧
      AggregateCallGraphRenderer.render functions target bindings (indent + 4) selected.nextId
        no = .ok fallback ∧
      (target ≠ .unit → rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("if (" ++ tested.value ++ ") {")] ++ selected.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ selected.value ++ ";"),
            indentLine indent "} else {"] ++
          fallback.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ fallback.value ++ ";"),
            indentLine indent "}"],
        temporary tested.nextId, fallback.nextId⟩) := by
  simp only [AggregateCallGraphRenderer.render] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  refine ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    fun valued => ?_⟩
  rw [← Except.ok.inj equation]
  cases target
  case unit => exact absurd rfl valued
  all_goals rfl

/-- `!` and `~` bind their result to a fresh temporary. -/
theorem unary (scalar : Target) (op : Solcore.Core.Wire.UnaryOp) (sourceOp : UnaryOp)
    (operand : CoreExpr) (selected : sourceUnary? op = some sourceOp) :
    AggregateCallGraphRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.unary op operand) =
      (AggregateCallGraphRenderer.render functions (if op == .boolNot then .bool else .word)
        bindings indent first operand).bind fun value =>
          .ok ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId)
              (LocalType.ofTarget scalar) (.unary sourceOp (.name value.value))),
            temporary value.nextId, value.nextId + 1⟩ := by
  cases op <;> simp only [sourceUnary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateCallGraphRenderer.render] <;> rfl

/-- `CLZ` snapshots its operand, then calls the raw opcode alias. -/
theorem clz (operand : CoreExpr) :
    AggregateCallGraphRenderer.render functions .word bindings indent first
        (.unary .wordClz operand) =
      (AggregateCallGraphRenderer.render functions .word bindings indent first operand).bind
        fun value =>
          .ok ⟨(snapshotOf indent value).lines ++ Stmt.lines indent
              (.letDecl (temporary (value.nextId + 1)) .word
                (.call1 "sc_clz" (.name (temporary value.nextId)))),
            temporary (value.nextId + 1), value.nextId + 2⟩ := by
  simp only [AggregateCallGraphRenderer.render]
  rfl

/-- The infix operations bind their result to a fresh temporary. -/
theorem binary (scalar : Target) (op : Solcore.Core.Wire.BinaryOp) (sourceOp : BinaryOp)
    (left right : CoreExpr) (selected : sourceBinary? op = some sourceOp) :
    AggregateCallGraphRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.binary op left right) =
      (AggregateCallGraphRenderer.render functions .word bindings indent first left).bind
        fun leftValue =>
          (AggregateCallGraphRenderer.render functions .word bindings indent leftValue.nextId
            right).bind fun rightValue =>
              .ok ⟨leftValue.lines ++ rightValue.lines ++ Stmt.lines indent
                  (.letDecl (temporary rightValue.nextId) (LocalType.ofTarget scalar)
                    (.binary sourceOp (.name leftValue.value) (.name rightValue.value))),
                temporary rightValue.nextId, rightValue.nextId + 1⟩ := by
  cases op <;> simp only [sourceBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateCallGraphRenderer.render] <;> rfl

/-- Extended binary operations snapshot both operands, left to right, then
call the raw opcode alias. -/
theorem binary_primitive (scalar : Target) (op : Solcore.Core.Wire.BinaryOp)
    (build : String → String → Expr) (left right : CoreExpr)
    (selected : primitiveBinary? op = some build) :
    AggregateCallGraphRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.binary op left right) =
      (AggregateCallGraphRenderer.render functions .word bindings indent first left).bind
        fun leftValue =>
          (AggregateCallGraphRenderer.render functions .word bindings indent
            (leftValue.nextId + 1) right).bind fun rightValue =>
              .ok ⟨(snapshotOf indent leftValue).lines ++ (snapshotOf indent rightValue).lines ++
                  Stmt.lines indent (.letDecl (temporary (rightValue.nextId + 1))
                    (LocalType.ofTarget scalar)
                    (build (temporary leftValue.nextId) (temporary rightValue.nextId))),
                temporary (rightValue.nextId + 1), rightValue.nextId + 2⟩ := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateCallGraphRenderer.render] <;> rfl

/-- `ADDMOD` and `MULMOD` snapshot all three operands, then call the raw
opcode alias. -/
theorem ternary (op : Solcore.Core.Wire.TernaryOp) (one two three : CoreExpr) :
    AggregateCallGraphRenderer.render functions .word bindings indent first
        (.ternary op one two three) =
      (AggregateCallGraphRenderer.render functions .word bindings indent first one).bind
        fun oneValue =>
          (AggregateCallGraphRenderer.render functions .word bindings indent
            (oneValue.nextId + 1) two).bind fun twoValue =>
              (AggregateCallGraphRenderer.render functions .word bindings indent
                (twoValue.nextId + 1) three).bind fun threeValue =>
                  .ok ⟨(snapshotOf indent oneValue).lines ++
                      (snapshotOf indent twoValue).lines ++
                      (snapshotOf indent threeValue).lines ++
                      Stmt.lines indent (.letDecl (temporary (threeValue.nextId + 1)) .word
                        (.call3 (ternaryCallee op) (.name (temporary oneValue.nextId))
                          (.name (temporary twoValue.nextId))
                          (.name (temporary threeValue.nextId)))),
                    temporary (threeValue.nextId + 1), threeValue.nextId + 2⟩ := by
  simp only [AggregateCallGraphRenderer.render]
  cases op <;> rfl

/-- A call to an earlier helper snapshots its argument, then calls the helper. -/
theorem apply_ok {index : Nat} {argument : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.apply (.var index) argument) = .ok rendered) :
    target = .word ∧ bindings.length ≤ index ∧ ∃ callee value,
      functions[index - bindings.length]? = some callee ∧
      AggregateCallGraphRenderer.render functions .word bindings indent first argument =
        .ok value ∧
      rendered = ⟨(snapshotOf indent value).lines ++ Stmt.lines indent
          (.letDecl (temporary (value.nextId + 1)) .word
            (.call1 callee (.name (temporary value.nextId)))),
        temporary (value.nextId + 1), value.nextId + 2⟩ := by
  cases target
  case word =>
    by_cases below : index < bindings.length
    · dsimp only [AggregateCallGraphRenderer.render] at equation
      rw [if_pos below] at equation
      cases equation
    · cases found : functions[index - bindings.length]? with
      | none =>
          dsimp only [AggregateCallGraphRenderer.render] at equation
          rw [if_neg below, found] at equation
          cases equation
      | some callee =>
          dsimp only [AggregateCallGraphRenderer.render] at equation
          rw [if_neg below, found] at equation
          obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
          exact ⟨rfl, Nat.le_of_not_lt below, callee, value, rfl, valueEquation,
            (Except.ok.inj equation).symm⟩
  all_goals cases equation

theorem pair_ok {left right : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.pair left right) = .ok rendered) :
    target = .wordPair ∧ ∃ leftValue rightValue,
      AggregateCallGraphRenderer.render functions .word bindings indent first left =
        .ok leftValue ∧
      AggregateCallGraphRenderer.render functions .word bindings indent leftValue.nextId right =
        .ok rightValue ∧
      rendered = ⟨leftValue.lines ++ rightValue.lines ++
          Stmt.lines indent (.letDecl (temporary rightValue.nextId) .wordPair
            (.tuple (.name leftValue.value) (.name rightValue.value))),
        temporary rightValue.nextId, rightValue.nextId + 1⟩ := by
  cases target
  case wordPair =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨leftValue, leftEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨rightValue, rightEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨rfl, leftValue, rightValue, leftEquation, rightEquation,
      (Except.ok.inj equation).symm⟩
  all_goals cases equation

theorem first_ok {operand : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.first operand) = .ok rendered) :
    target = .word ∧ ∃ operandValue,
      AggregateCallGraphRenderer.render functions .wordPair bindings indent first operand =
        .ok operandValue ∧
      rendered = ⟨operandValue.lines ++ Stmt.listLines indent
          (projectionStmts operandValue.nextId operandValue.value (operandValue.nextId + 1)),
        temporary operandValue.nextId, operandValue.nextId + 3⟩ := by
  cases target
  case word =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨operandValue, operandEquation, equation⟩ := except_bind_eq_ok equation
    refine ⟨rfl, operandValue, operandEquation, ?_⟩
    rw [← Except.ok.inj equation]
    show (⟨operandValue.lines ++ _ ++ _, _, _⟩ : ScalarRenderer.Rendered) = _
    simp only [List.append_assoc]
    rfl
  all_goals cases equation

theorem second_ok {operand : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.second operand) = .ok rendered) :
    target = .word ∧ ∃ operandValue,
      AggregateCallGraphRenderer.render functions .wordPair bindings indent first operand =
        .ok operandValue ∧
      rendered = ⟨operandValue.lines ++ Stmt.listLines indent
          (projectionStmts operandValue.nextId operandValue.value (operandValue.nextId + 2)),
        temporary operandValue.nextId, operandValue.nextId + 3⟩ := by
  cases target
  case word =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨operandValue, operandEquation, equation⟩ := except_bind_eq_ok equation
    refine ⟨rfl, operandValue, operandEquation, ?_⟩
    rw [← Except.ok.inj equation]
    show (⟨operandValue.lines ++ _ ++ _, _, _⟩ : ScalarRenderer.Rendered) = _
    simp only [List.append_assoc]
    rfl
  all_goals cases equation

theorem inLeft_ok {payload : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.inLeft .word payload) = .ok rendered) :
    target = .wordSum ∧ ∃ payloadValue,
      AggregateCallGraphRenderer.render functions .word bindings indent first payload =
        .ok payloadValue ∧
      rendered = ⟨payloadValue.lines ++ Stmt.lines indent
          (.letDecl (temporary payloadValue.nextId) .wordSum (.inl (.name payloadValue.value))),
        temporary payloadValue.nextId, payloadValue.nextId + 1⟩ := by
  cases target
  case wordSum =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨payloadValue, payloadEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨rfl, payloadValue, payloadEquation, (Except.ok.inj equation).symm⟩
  all_goals cases equation

theorem inRight_ok {payload : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.inRight .word payload) = .ok rendered) :
    target = .wordSum ∧ ∃ payloadValue,
      AggregateCallGraphRenderer.render functions .word bindings indent first payload =
        .ok payloadValue ∧
      rendered = ⟨payloadValue.lines ++ Stmt.lines indent
          (.letDecl (temporary payloadValue.nextId) .wordSum (.inr (.name payloadValue.value))),
        temporary payloadValue.nextId, payloadValue.nextId + 1⟩ := by
  cases target
  case wordSum =>
    simp only [AggregateCallGraphRenderer.render] at equation
    obtain ⟨payloadValue, payloadEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨rfl, payloadValue, payloadEquation, (Except.ok.inj equation).symm⟩
  all_goals cases equation

theorem caseE_ok {scrutinee yes no : CoreExpr}
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      (.caseE scrutinee yes no) = .ok rendered) :
    ∃ tested selected fallback,
      AggregateCallGraphRenderer.render functions .wordSum bindings indent first scrutinee =
        .ok tested ∧
      AggregateCallGraphRenderer.render functions target
        (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
          yes = .ok selected ∧
      AggregateCallGraphRenderer.render functions target
        (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
          no = .ok fallback ∧
      (target ≠ .unit → rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("match (" ++ tested.value ++ ") {"),
            indentLine (indent + 4) ("case inl(" ++ payloadTemp (tested.nextId + 1) ++ ") {")] ++
          (selected.lines ++ [indentLine (indent + 8)
            (temporary tested.nextId ++ " = " ++ selected.value ++ ";")]) ++
          [indentLine (indent + 4) "}",
            indentLine (indent + 4)
              ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
          (fallback.lines ++ [indentLine (indent + 8)
            (temporary tested.nextId ++ " = " ++ fallback.value ++ ";")]) ++
          [indentLine (indent + 4) "}", indentLine indent "}"],
        temporary tested.nextId, fallback.nextId⟩) := by
  simp only [AggregateCallGraphRenderer.render] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  refine ⟨tested, selected, fallback, testedEquation, selectedEquation, fallbackEquation,
    fun valued => ?_⟩
  rw [← Except.ok.inj equation]
  cases target
  case unit => exact absurd rfl valued
  all_goals
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-- The renderer rejects Unit, cells, integers, closures, data and indirect
calls outright. -/
theorem rejected {expression : CoreExpr}
    (rejects : expression = .unit ∨ (∃ value, expression = .integer value) ∨
      (∃ parameterType resultType body, expression = .lambda parameterType resultType body) ∨
      (∃ elementType inner, expression = .newCell elementType inner) ∨
      (∃ reference, expression = .loadCell reference) ∨
      (∃ reference value, expression = .storeCell reference value) ∨
      (∃ constructor payload, expression = .construct constructor payload) ∨
      (∃ dataType resultType scrutinee branches,
        expression = .matchData dataType resultType scrutinee branches))
    (equation : AggregateCallGraphRenderer.render functions target bindings indent first
      expression = .ok rendered) : False := by
  rcases rejects with rfl | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ |
    ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> cases equation

end AggregateCallGraphEquations

end Solcore.Synthesis.Source.ScalarMeaning
