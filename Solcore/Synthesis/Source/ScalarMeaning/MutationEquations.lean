import Solcore.Synthesis.Source.ScalarMeaning.MutationSpec
import Solcore.Synthesis.Source.ScalarMeaning.RendererEquations

/-! Equations for the actual `MutationRenderer.render`, stated with the scalar
source syntax and printer, and inversions of the mutation profile's acceptance
check `initializerKind?`. Private helpers of the renderer and of the profile are
unfolded by definitional equality; nothing here re-implements them. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.MutationRenderer (Binding)
open Solcore.Synthesis.Core.LocalMutation (Local initializerKind? infer?)
/-- The source type of a scalar mutation target. -/
def MTarget.localType : MTarget → LocalType
  | .bool => .bool
  | _ => .word

/-- The scalar target of a Word or Boolean mutation target. -/
def MTarget.scalar : MTarget → Solcore.Synthesis.Core.Target
  | .bool => .bool
  | _ => .word

/-- The binding a Word or Boolean `let` introduces. -/
def letBinding : MTarget → String → Binding
  | .word, name => .word name
  | .bool, name => .bool name
  | .unit, _ => .unit

theorem requireValue_ok {rendered : MRendered} {value : String}
    (equation : MutationRenderer.requireValue rendered = .ok value) :
    rendered.value = some value := by
  unfold MutationRenderer.requireValue at equation
  cases found : rendered.value with
  | none =>
      rw [found] at equation
      cases equation
  | some value' =>
      rw [found] at equation
      cases equation
      rfl

theorem cellDecl_lines (indent : Nat) (name value : String) :
    [indentLine indent ("let " ++ name ++ ": word = " ++ value ++ ";")] =
      Stmt.lines indent (.letDecl name .word (.name value)) := by
  simp only [Stmt.lines, LocalType.spelling, Expr.print, List.cons.injEq, and_true]
  congr 1
  apply String.toList_inj.mp
  simp

/-- The scalar target of a mutation target, as the renderer computes it. -/
def MTarget.scalarExcept : MTarget → Except EmitError Solcore.Synthesis.Core.Target
  | .word => .ok .word
  | .bool => .ok .bool
  | .unit => .error (.unsupportedExpression "Unit used as a scalar target")

namespace MutationEquations

variable {functions : List String} {target : MTarget} {bindings : List Binding}
  {indent first : Nat} {rendered : MRendered}

theorem word (value : Solcore.Core.Word) :
    MutationRenderer.render functions target bindings indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        some (temporary first), first + 1⟩ := by
  simp only [MutationRenderer.render]
  rfl

theorem bool (value : Bool) :
    MutationRenderer.render functions target bindings indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        some (temporary first), first + 1⟩ := by
  simp only [MutationRenderer.render]
  rfl

theorem unit :
    MutationRenderer.render functions target bindings indent first .unit =
      .ok ⟨[], none, first⟩ := by
  simp only [MutationRenderer.render]

theorem var_ok {index : Nat}
    (equation : MutationRenderer.render functions target bindings indent first (.var index) =
      .ok rendered) :
    (∃ name, (bindings[index]? = some (Binding.word name) ∨
        bindings[index]? = some (Binding.bool name)) ∧ rendered = ⟨[], some name, first⟩) ∨
      (bindings[index]? = some Binding.unit ∧ rendered = ⟨[], none, first⟩) := by
  simp only [MutationRenderer.render] at equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      cases binding with
      | word name => exact Or.inl ⟨name, Or.inl rfl, (Except.ok.inj equation).symm⟩
      | bool name => exact Or.inl ⟨name, Or.inr rfl, (Except.ok.inj equation).symm⟩
      | unit => exact Or.inr ⟨rfl, (Except.ok.inj equation).symm⟩
      | cellWord name => cases equation

theorem newCellLet_ok {initializer body : CoreExpr}
    (equation : MutationRenderer.render functions target bindings indent first
      (.letE (.newCell .word initializer) body) = .ok rendered) :
    ∃ initial value rest,
      MutationRenderer.render functions .word bindings indent first initializer = .ok initial ∧
      initial.value = some value ∧
      MutationRenderer.render functions target (.cellWord (cellTemp initial.nextId) :: bindings)
        indent (initial.nextId + 1) body = .ok rest ∧
      rendered = ⟨initial.lines ++
        Stmt.lines indent (.letDecl (cellTemp initial.nextId) .word (.name value)) ++ rest.lines,
        rest.value, rest.nextId⟩ := by
  simp only [MutationRenderer.render] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  refine ⟨initial, value, rest, initialEquation, requireValue_ok valueEquation, restEquation, ?_⟩
  rw [← cellDecl_lines]
  exact (Except.ok.inj equation).symm

theorem letE_infer {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (equation : MutationRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ kind, infer? (bindings.map Binding.kind) functions.length initializer = some kind := by
  rw [MutationRenderer.render.eq_6 _ _ _ _ _ _ _ notCell] at equation
  cases inferred : infer? (bindings.map Binding.kind) functions.length initializer with
  | none =>
      rw [inferred] at equation
      cases equation
  | some kind => exact ⟨kind, rfl⟩

theorem letE_unit_ok {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (inferred : infer? (bindings.map Binding.kind) functions.length initializer = some .unit)
    (equation : MutationRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ initial rest,
      MutationRenderer.render functions .unit bindings indent first initializer = .ok initial ∧
      MutationRenderer.render functions target (.unit :: bindings) indent initial.nextId body =
        .ok rest ∧
      rendered = ⟨initial.lines ++ rest.lines, rest.value, rest.nextId⟩ := by
  rw [MutationRenderer.render.eq_6 _ _ _ _ _ _ _ notCell, inferred] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨initial, rest, initialEquation, restEquation, (Except.ok.inj equation).symm⟩

theorem letE_value_ok {initializer body : CoreExpr} {kind : MTarget}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (scalarKind : kind = .word ∨ kind = .bool)
    (inferred : infer? (bindings.map Binding.kind) functions.length initializer = some kind)
    (equation : MutationRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ initial value rest,
      MutationRenderer.render functions kind bindings indent first initializer = .ok initial ∧
      initial.value = some value ∧
      MutationRenderer.render functions target (letBinding kind (temporary initial.nextId) ::
        bindings) indent (initial.nextId + 1) body = .ok rest ∧
      rendered = ⟨initial.lines ++
        Stmt.lines indent (.letDecl (temporary initial.nextId) kind.localType (.name value)) ++
        rest.lines, rest.value, rest.nextId⟩ := by
  rw [MutationRenderer.render.eq_6 _ _ _ _ _ _ _ notCell, inferred] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  rcases scalarKind with rfl | rfl <;>
  · obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨initial, value, rest, initialEquation, requireValue_ok valueEquation, restEquation,
      (Except.ok.inj equation).symm⟩

theorem loadCell_ok {index : Nat}
    (equation : MutationRenderer.render functions target bindings indent first
      (.loadCell (.var index)) = .ok rendered) :
    ∃ name, bindings[index]? = some (Binding.cellWord name) ∧
      rendered = ⟨Stmt.lines indent (.letDecl (temporary first) .word (.name name)),
        some (temporary first), first + 1⟩ := by
  have unfolded : ((match bindings[index]? with
      | some (Binding.cellWord name) => (Except.ok name : Except EmitError String)
      | _ => .error (.unsupportedExpression "cell reference is not a direct private local")).bind
        fun name => Except.ok (⟨Stmt.lines indent (.letDecl (temporary first) .word (.name name)),
          some (temporary first), first + 1⟩ : MRendered)) = .ok rendered := equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at unfolded
      cases unfolded
  | some binding =>
      rw [found] at unfolded
      cases binding with
      | cellWord name => exact ⟨name, rfl, (Except.ok.inj unfolded).symm⟩
      | word name => cases unfolded
      | bool name => cases unfolded
      | unit => cases unfolded

theorem unary_ok {op : Solcore.Core.Wire.UnaryOp} {sourceOp : UnaryOp} {operand : CoreExpr}
    (selected : sourceUnary? op = some sourceOp)
    (equation : MutationRenderer.render functions target bindings indent first
      (.unary op operand) = .ok rendered) :
    ∃ operandRendered value scalarTarget,
      MutationRenderer.render functions (if op == .boolNot then .bool else .word) bindings indent
        first operand = .ok operandRendered ∧
      operandRendered.value = some value ∧ target.scalarExcept = .ok scalarTarget ∧
      rendered = ⟨operandRendered.lines ++ Stmt.lines indent (.letDecl
          (temporary operandRendered.nextId) (LocalType.ofTarget scalarTarget)
          (.unary sourceOp (.name value))),
        some (temporary operandRendered.nextId), operandRendered.nextId + 1⟩ := by
  have unfolded : ((MutationRenderer.render functions (if op == .boolNot then (.bool : MTarget)
      else .word) bindings indent first operand).bind fun operandRendered =>
      (MutationRenderer.requireValue operandRendered).bind fun value =>
        (target.scalarExcept.bind fun scalarTarget =>
          (ScalarRenderer.render scalarTarget [value] indent operandRendered.nextId
            (.unary op (.var 0))).bind fun result =>
              Except.ok (⟨result.lines, some result.value, result.nextId⟩ : MRendered)).bind
          fun result => Except.ok (⟨operandRendered.lines ++ result.lines, result.value,
            result.nextId⟩ : MRendered)) = .ok rendered := by
    rw [← equation]
    cases target <;> rfl
  obtain ⟨operandRendered, operandEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨value, valueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨result, resultEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨scalarTarget, scalarEquation, resultEquation⟩ := except_bind_eq_ok resultEquation
  obtain ⟨scalarResult, scalarResultEquation, resultEquation⟩ := except_bind_eq_ok resultEquation
  simp only [ScalarRenderer.render] at scalarResultEquation
  rw [RendererEquations.unary, selected] at scalarResultEquation
  obtain ⟨operandValue, operandValueEquation, scalarResultEquation⟩ :=
    except_bind_eq_ok scalarResultEquation
  rw [RendererEquations.var] at operandValueEquation
  simp only [List.getElem?_cons_zero] at operandValueEquation
  cases operandValueEquation
  cases scalarResultEquation
  cases resultEquation
  cases unfolded
  exact ⟨operandRendered, value, scalarTarget, operandEquation, requireValue_ok valueEquation,
    scalarEquation, rfl⟩

theorem storeCell_ok {index : Nat} {value : CoreExpr}
    (equation : MutationRenderer.render functions target bindings indent first
      (.storeCell (.var index) value) = .ok rendered) :
    ∃ name written result, bindings[index]? = some (Binding.cellWord name) ∧
      MutationRenderer.render functions .word bindings indent first value = .ok written ∧
      written.value = some result ∧
      rendered = ⟨written.lines ++ Stmt.lines indent (.assign name (.name result)), none,
        written.nextId⟩ := by
  have unfolded : ((match bindings[index]? with
      | some (Binding.cellWord name) => (Except.ok name : Except EmitError String)
      | _ => .error (.unsupportedExpression "cell reference is not a direct private local")).bind
        fun name => (MutationRenderer.render functions .word bindings indent first value).bind
          fun written => (MutationRenderer.requireValue written).bind fun result =>
            Except.ok (⟨written.lines ++ Stmt.lines indent (.assign name (.name result)), none,
              written.nextId⟩ : MRendered)) = .ok rendered := equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at unfolded
      cases unfolded
  | some binding =>
      rw [found] at unfolded
      cases binding with
      | cellWord name =>
          obtain ⟨name', nameEquation, unfolded⟩ := except_bind_eq_ok unfolded
          cases nameEquation
          obtain ⟨written, writtenEquation, unfolded⟩ := except_bind_eq_ok unfolded
          obtain ⟨result, resultEquation, unfolded⟩ := except_bind_eq_ok unfolded
          exact ⟨name, written, result, rfl, writtenEquation, requireValue_ok resultEquation,
            (Except.ok.inj unfolded).symm⟩
      | word name => cases unfolded
      | bool name => cases unfolded
      | unit => cases unfolded

theorem binary_ok {op : Solcore.Core.Wire.BinaryOp} {sourceOp : BinaryOp} {left right : CoreExpr}
    (selected : sourceBinary? op = some sourceOp)
    (equation : MutationRenderer.render functions target bindings indent first
      (.binary op left right) = .ok rendered) :
    ∃ leftRendered leftValue rightRendered rightValue scalarTarget,
      MutationRenderer.render functions .word bindings indent first left = .ok leftRendered ∧
      leftRendered.value = some leftValue ∧
      MutationRenderer.render functions .word bindings indent leftRendered.nextId right =
        .ok rightRendered ∧
      rightRendered.value = some rightValue ∧ target.scalarExcept = .ok scalarTarget ∧
      rendered = ⟨leftRendered.lines ++ rightRendered.lines ++ Stmt.lines indent (.letDecl
          (temporary rightRendered.nextId) (LocalType.ofTarget scalarTarget)
          (.binary sourceOp (.name leftValue) (.name rightValue))),
        some (temporary rightRendered.nextId), rightRendered.nextId + 1⟩ := by
  have unfolded : ((MutationRenderer.render functions .word bindings indent first left).bind
      fun leftRendered => (MutationRenderer.requireValue leftRendered).bind fun leftValue =>
        (MutationRenderer.render functions .word bindings indent leftRendered.nextId right).bind
          fun rightRendered => (MutationRenderer.requireValue rightRendered).bind
            fun rightValue => (target.scalarExcept.bind fun scalarTarget =>
              (ScalarRenderer.render scalarTarget [leftValue, rightValue] indent
                rightRendered.nextId (.binary op (.var 0) (.var 1))).bind fun result =>
                  Except.ok (⟨result.lines, some result.value, result.nextId⟩ : MRendered)).bind
              fun result => Except.ok (⟨leftRendered.lines ++ rightRendered.lines ++
                result.lines, result.value, result.nextId⟩ : MRendered)) = .ok rendered := by
    rw [← equation]
    cases target <;> rfl
  obtain ⟨leftRendered, leftEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨leftValue, leftValueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨rightRendered, rightEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨rightValue, rightValueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨result, resultEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨scalarTarget, scalarEquation, resultEquation⟩ := except_bind_eq_ok resultEquation
  obtain ⟨scalarResult, scalarResultEquation, resultEquation⟩ := except_bind_eq_ok resultEquation
  simp only [ScalarRenderer.render] at scalarResultEquation
  rw [RendererEquations.binary, selected] at scalarResultEquation
  obtain ⟨first, firstEquation, scalarResultEquation⟩ := except_bind_eq_ok scalarResultEquation
  obtain ⟨second, secondEquation, scalarResultEquation⟩ := except_bind_eq_ok scalarResultEquation
  rw [RendererEquations.var] at firstEquation secondEquation
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at firstEquation secondEquation
  cases firstEquation
  cases secondEquation
  cases scalarResultEquation
  cases resultEquation
  cases unfolded
  exact ⟨leftRendered, leftValue, rightRendered, rightValue, scalarTarget, leftEquation,
    requireValue_ok leftValueEquation, rightEquation, requireValue_ok rightValueEquation,
    scalarEquation, rfl⟩

theorem apply_ok {index : Nat} {argument : CoreExpr}
    (equation : MutationRenderer.render functions target bindings indent first
      (.apply (.var index) argument) = .ok rendered) :
    bindings.length ≤ index ∧ ∃ callee argumentRendered value,
      functions[index - bindings.length]? = some callee ∧
      MutationRenderer.render functions .word bindings indent first argument =
        .ok argumentRendered ∧
      argumentRendered.value = some value ∧
      rendered = ⟨argumentRendered.lines ++ Stmt.lines indent (.letDecl
          (temporary argumentRendered.nextId) .word (.call1 callee (.name value))),
        some (temporary argumentRendered.nextId), argumentRendered.nextId + 1⟩ := by
  by_cases below : index < bindings.length
  · dsimp only [MutationRenderer.render] at equation
    rw [if_pos below] at equation
    cases equation
  · cases found : functions[index - bindings.length]? with
    | none =>
        dsimp only [MutationRenderer.render] at equation
        rw [if_neg below, found] at equation
        cases equation
    | some callee =>
        dsimp only [MutationRenderer.render] at equation
        rw [if_neg below, found] at equation
        obtain ⟨argumentRendered, argumentEquation, equation⟩ := except_bind_eq_ok equation
        obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
        exact ⟨Nat.le_of_not_lt below, callee, argumentRendered, value, rfl, argumentEquation,
          requireValue_ok valueEquation, (Except.ok.inj equation).symm⟩

theorem ifE_unit_ok {condition yes no : CoreExpr}
    (equation : MutationRenderer.render functions .unit bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested conditionValue selected fallback,
      MutationRenderer.render functions .bool bindings indent first condition = .ok tested ∧
      tested.value = some conditionValue ∧
      MutationRenderer.render functions .unit bindings (indent + 4) tested.nextId yes =
        .ok selected ∧
      MutationRenderer.render functions .unit bindings (indent + 4) selected.nextId no =
        .ok fallback ∧
      rendered = ⟨tested.lines ++ [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++
        selected.lines ++ [indentLine indent "} else {"] ++ fallback.lines ++
        [indentLine indent "}"], none, fallback.nextId⟩ := by
  simp only [MutationRenderer.render] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨conditionValue, conditionEquation, equation⟩ := except_bind_eq_ok equation
  have unitTest : ((.unit : MTarget) == .unit) = true := rfl
  rw [if_pos unitTest] at equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨tested, conditionValue, selected, fallback, testedEquation,
    requireValue_ok conditionEquation, selectedEquation, fallbackEquation,
    (Except.ok.inj equation).symm⟩

theorem ifE_value_ok {condition yes no : CoreExpr} (scalar : target = .word ∨ target = .bool)
    (equation : MutationRenderer.render functions target bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested conditionValue selected selectedValue fallback fallbackValue,
      MutationRenderer.render functions .bool bindings indent first condition = .ok tested ∧
      tested.value = some conditionValue ∧
      MutationRenderer.render functions target bindings (indent + 4) (tested.nextId + 1) yes =
        .ok selected ∧
      selected.value = some selectedValue ∧
      MutationRenderer.render functions target bindings (indent + 4) selected.nextId no =
        .ok fallback ∧
      fallback.value = some fallbackValue ∧
      rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ zeroText target.scalar ++ ";")] ++
          [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++ selected.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";"),
            indentLine indent "} else {"] ++
          fallback.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";"),
            indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  rcases scalar with rfl | rfl <;>
  · simp only [MutationRenderer.render] at equation
    obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨conditionValue, conditionEquation, equation⟩ := except_bind_eq_ok equation
    rw [if_neg (by decide)] at equation
    obtain ⟨resultValue, resultEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨selectedValue, selectedValueEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨fallbackValue, fallbackValueEquation, equation⟩ := except_bind_eq_ok equation
    have resultName : resultValue = temporary tested.nextId :=
      (Option.some.inj (requireValue_ok resultEquation)).symm
    subst resultName
    exact ⟨tested, conditionValue, selected, selectedValue, fallback, fallbackValue,
      testedEquation, requireValue_ok conditionEquation, selectedEquation,
      requireValue_ok selectedValueEquation, fallbackEquation,
      requireValue_ok fallbackValueEquation, (Except.ok.inj equation).symm⟩

theorem unary_unsupported {op : Solcore.Core.Wire.UnaryOp} {operand : CoreExpr}
    (unsupported : sourceUnary? op = none)
    (equation : MutationRenderer.render functions target bindings indent first
      (.unary op operand) = .ok rendered) : False := by
  have unfolded : ((MutationRenderer.render functions (if op == .boolNot then (.bool : MTarget)
      else .word) bindings indent first operand).bind fun operandRendered =>
      (MutationRenderer.requireValue operandRendered).bind fun value =>
        (target.scalarExcept.bind fun scalarTarget =>
          (ScalarRenderer.render scalarTarget [value] indent operandRendered.nextId
            (.unary op (.var 0))).bind fun result =>
              Except.ok (⟨result.lines, some result.value, result.nextId⟩ : MRendered)).bind
          fun result => Except.ok (⟨operandRendered.lines ++ result.lines, result.value,
            result.nextId⟩ : MRendered)) = .ok rendered := by
    rw [← equation]
    cases target <;> rfl
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, resultEquation, _⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, resultEquation⟩ := except_bind_eq_ok resultEquation
  obtain ⟨_, scalarResultEquation, _⟩ := except_bind_eq_ok resultEquation
  simp only [ScalarRenderer.render] at scalarResultEquation
  rw [RendererEquations.unary, unsupported] at scalarResultEquation
  cases scalarResultEquation

theorem binary_unsupported {op : Solcore.Core.Wire.BinaryOp} {left right : CoreExpr}
    (unsupported : sourceBinary? op = none)
    (equation : MutationRenderer.render functions target bindings indent first
      (.binary op left right) = .ok rendered) : False := by
  have unfolded : ((MutationRenderer.render functions .word bindings indent first left).bind
      fun leftRendered => (MutationRenderer.requireValue leftRendered).bind fun leftValue =>
        (MutationRenderer.render functions .word bindings indent leftRendered.nextId right).bind
          fun rightRendered => (MutationRenderer.requireValue rightRendered).bind
            fun rightValue => (target.scalarExcept.bind fun scalarTarget =>
              (ScalarRenderer.render scalarTarget [leftValue, rightValue] indent
                rightRendered.nextId (.binary op (.var 0) (.var 1))).bind fun result =>
                  Except.ok (⟨result.lines, some result.value, result.nextId⟩ : MRendered)).bind
              fun result => Except.ok (⟨leftRendered.lines ++ rightRendered.lines ++
                result.lines, result.value, result.nextId⟩ : MRendered)) = .ok rendered := by
    rw [← equation]
    cases target <;> rfl
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, resultEquation, _⟩ := except_bind_eq_ok unfolded
  obtain ⟨_, _, resultEquation⟩ := except_bind_eq_ok resultEquation
  obtain ⟨_, scalarResultEquation, _⟩ := except_bind_eq_ok resultEquation
  simp only [ScalarRenderer.render] at scalarResultEquation
  rw [RendererEquations.binary, unsupported] at scalarResultEquation
  cases scalarResultEquation

end MutationEquations

namespace MutationKinds

theorem local_beq (first second : Local) : (first == second) = decide (first = second) := by
  cases first <;> cases second <;> rfl


theorem infer_toLocal {locals : List Local} {prior : Nat} {expression : CoreExpr}
    {kind : Solcore.Synthesis.Core.LocalMutation.Target}
    (inferred : infer? locals prior expression = some kind) :
    initializerKind? locals prior expression = some kind.toLocal := by
  have unfolded : (initializerKind? locals prior expression).bind Local.toTarget? = some kind :=
    inferred
  cases found : initializerKind? locals prior expression with
  | none =>
      rw [found] at unfolded
      cases unfolded
  | some found' =>
      rw [found] at unfolded
      cases found' <;> cases unfolded <;> rfl

theorem toLocal_infer {locals : List Local} {prior : Nat} {expression : CoreExpr}
    {kind : Solcore.Synthesis.Core.LocalMutation.Target}
    (inferred : initializerKind? locals prior expression = some kind.toLocal) :
    infer? locals prior expression = some kind := by
  show (initializerKind? locals prior expression).bind Local.toTarget? = some kind
  rw [inferred]
  cases kind <;> rfl

theorem var {locals : List Local} {prior index : Nat} {kind : Local}
    (inferred : initializerKind? locals prior (.var index) = some kind) :
    locals[index]? = some kind ∧ kind ≠ .cellWord := by
  have unfolded : ((locals[index]?).bind fun found =>
      if found == Local.cellWord then none else some found) = some kind := inferred
  cases found : locals[index]? with
  | none =>
      rw [found] at unfolded
      cases unfolded
  | some found' =>
      rw [found] at unfolded
      cases found' <;> simp [local_beq] at unfolded <;> subst unfolded <;> simp

theorem letE {locals : List Local} {prior : Nat} {initializer body : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.letE initializer body) = some result) :
    ∃ kind, initializerKind? locals prior initializer = some kind ∧
      initializerKind? (kind :: locals) prior body = some result ∧ result ≠ .cellWord := by
  have unfolded : ((initializerKind? locals prior initializer).bind fun kind =>
      (initializerKind? (kind :: locals) prior body).bind fun result =>
        if result == Local.cellWord then none else some result) = some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨kind, initializerKind, result', bodyKind, last⟩ := unfolded
  cases result' <;> simp [local_beq] at last <;> subst last <;>
    exact ⟨kind, initializerKind, bodyKind, by simp⟩

theorem newCell {locals : List Local} {prior : Nat} {inner : CoreExpr} {kind : Local}
    (inferred : initializerKind? locals prior (.newCell .word inner) = some kind) :
    kind = .cellWord ∧ initializerKind? locals prior inner = some .word := by
  have unfolded : ((initializerKind? locals prior inner).bind fun found =>
      (if found == Local.word then some () else none).bind fun _ => some Local.cellWord) =
      some kind := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, innerKind, checked, check, last⟩ := unfolded
  cases last
  cases found <;> simp [local_beq] at check
  exact ⟨rfl, innerKind⟩

/-- The local kind of a scalar result. -/
def scalarKind : Solcore.Synthesis.Core.Target → Local
  | .word => .word
  | .bool => .bool

theorem ifE {locals : List Local} {prior : Nat} {condition yes no : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.ifE condition yes no) = some result) :
    initializerKind? locals prior condition = some .bool ∧
      initializerKind? locals prior yes = some result ∧
      initializerKind? locals prior no = some result ∧ result ≠ .cellWord := by
  have unfolded : ((initializerKind? locals prior condition).bind fun found =>
      (if found == Local.bool then some () else none).bind fun _ =>
        (initializerKind? locals prior yes).bind fun left =>
          (initializerKind? locals prior no).bind fun right =>
            if (left == right && left != Local.cellWord) = true then some left else none) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, conditionKind, checked, check, left, yesKind, right, noKind, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases left <;> cases right <;> simp [local_beq, bne] at last <;> subst last <;>
    exact ⟨conditionKind, yesKind, noKind, by simp⟩

theorem loadCell {locals : List Local} {prior index : Nat} {result : Local}
    (inferred : initializerKind? locals prior (.loadCell (.var index)) = some result) :
    locals[index]? = some .cellWord ∧ result = .word := by
  have unfolded : ((locals[index]?).bind fun found =>
      (if found == Local.cellWord then some () else none).bind fun _ => some Local.word) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, foundEq, checked, check, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases last
  exact ⟨foundEq, rfl⟩

theorem storeCell {locals : List Local} {prior index : Nat} {value : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.storeCell (.var index) value) = some result) :
    locals[index]? = some .cellWord ∧ initializerKind? locals prior value = some .word ∧
      result = .unit := by
  have unfolded : ((locals[index]?).bind fun found =>
      (if found == Local.cellWord then some () else none).bind fun _ =>
        (initializerKind? locals prior value).bind fun written =>
          (if written == Local.word then some () else none).bind fun _ => some Local.unit) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, foundEq, checked, check, written, valueKind, checked', check', last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases written <;> simp [local_beq] at check'
  cases last
  exact ⟨foundEq, valueKind, rfl⟩

/-- The integer operations, which the mutation profile rejects. -/
def integerUnary : Solcore.Core.Wire.UnaryOp → Bool
  | .integerNot | .integerToWord | .wordToInteger => true
  | _ => false

def integerBinary : Solcore.Core.Wire.BinaryOp → Bool
  | .integerAdd | .integerSub | .integerMul | .integerDiv | .integerMod
  | .integerEq | .integerLt | .integerAnd | .integerOr | .integerXor => true
  | _ => false

theorem unary_eq (locals : List Local) (prior : Nat) (op : Solcore.Core.Wire.UnaryOp)
    (operand : CoreExpr) :
    initializerKind? locals prior (.unary op operand) =
      if integerUnary op then none else
        (initializerKind? locals prior operand).bind fun found =>
          (if found == scalarKind (Target.unaryOperand op) then some () else none).bind fun _ =>
            some (scalarKind (Target.unaryResult op)) := by
  cases op <;> rfl

theorem binary_eq (locals : List Local) (prior : Nat) (op : Solcore.Core.Wire.BinaryOp)
    (left right : CoreExpr) :
    initializerKind? locals prior (.binary op left right) =
      if integerBinary op then none else
        (initializerKind? locals prior left).bind fun found =>
          (if found == Local.word then some () else none).bind fun _ =>
            (initializerKind? locals prior right).bind fun found' =>
              (if found' == Local.word then some () else none).bind fun _ =>
                some (scalarKind (Target.binaryResult op)) := by
  cases op <;> rfl

theorem unary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.UnaryOp}
    {sourceOp : UnaryOp} {operand : CoreExpr} {result : Local}
    (selected : sourceUnary? op = some sourceOp)
    (inferred : initializerKind? locals prior (.unary op operand) = some result) :
    initializerKind? locals prior operand = some (scalarKind (Target.unaryOperand op)) ∧
      result = scalarKind (Target.unaryResult op) := by
  have notInteger : integerUnary op = false := by
    cases op <;> simp_all [sourceUnary?, integerUnary]
  rw [unary_eq, if_neg (by simp [notInteger])] at inferred
  simp only [Option.bind_eq_some_iff] at inferred
  obtain ⟨found, operandKind, checked, check, last⟩ := inferred
  have same : found = scalarKind (Target.unaryOperand op) := by
    by_cases same : found = scalarKind (Target.unaryOperand op)
    · exact same
    · rw [local_beq, decide_eq_false same] at check
      cases check
  cases last
  exact ⟨same ▸ operandKind, rfl⟩

theorem binary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.BinaryOp}
    {sourceOp : BinaryOp} {left right : CoreExpr} {result : Local}
    (selected : sourceBinary? op = some sourceOp)
    (inferred : initializerKind? locals prior (.binary op left right) = some result) :
    initializerKind? locals prior left = some .word ∧
      initializerKind? locals prior right = some .word ∧
      result = scalarKind (Target.binaryResult op) := by
  have notInteger : integerBinary op = false := by
    cases op <;> simp_all [sourceBinary?, integerBinary]
  rw [binary_eq, if_neg (by simp [notInteger])] at inferred
  simp only [Option.bind_eq_some_iff] at inferred
  obtain ⟨found, leftKind, checked, check, found', rightKind, checked', check', last⟩ := inferred
  cases found <;> simp [local_beq] at check
  cases found' <;> simp [local_beq] at check'
  cases last
  exact ⟨leftKind, rightKind, rfl⟩

theorem apply {locals : List Local} {prior index : Nat} {argument : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.apply (.var index) argument) = some result) :
    locals.length ≤ index ∧ index < locals.length + prior ∧
      initializerKind? locals prior argument = some .word ∧ result = .word := by
  have unfolded : (if (decide (locals.length ≤ index) &&
      decide (index < locals.length + prior)) = true then
        (initializerKind? locals prior argument).bind fun found =>
          (if found == Local.word then some () else none).bind fun _ => some Local.word
      else none) = some result := inferred
  by_cases range : (decide (locals.length ≤ index) && decide (index < locals.length + prior)) = true
  · rw [if_pos range] at unfolded
    simp only [Bool.and_eq_true, decide_eq_true_eq] at range
    simp only [Option.bind_eq_some_iff] at unfolded
    obtain ⟨found, argumentKind, checked, check, last⟩ := unfolded
    cases found <;> simp [local_beq] at check
    cases last
    exact ⟨range.1, range.2, argumentKind, rfl⟩
  · rw [if_neg range] at unfolded
    cases unfolded

end MutationKinds
end Solcore.Synthesis.Source.ScalarMeaning
