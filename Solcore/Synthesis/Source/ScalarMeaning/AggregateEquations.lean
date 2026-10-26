import Solcore.Synthesis.Source.ScalarMeaning.AggregateSpec
import Solcore.Synthesis.Source.ScalarMeaning.CallGraphEquations
import Solcore.Synthesis.Source.ScalarMeaning.MutationEquations

/-! Equations for the actual `AggregateRenderer.render`, stated with the source
syntax and printer, and inversions of the aggregate profile's acceptance check
`initializerKind?`. Private helpers of the renderer and of the profile are
unfolded by definitional equality; nothing here re-implements them. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core (Target)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind? infer?)

/-- The aggregate target of a scalar target. -/
def ATarget.ofScalar : Target → ATarget
  | .word => .word
  | .bool => .bool

theorem ATarget.ofScalar_localType (scalar : Target) :
    (ATarget.ofScalar scalar).localType = LocalType.ofTarget scalar := by
  cases scalar <;> rfl

theorem ATarget.ofScalar_ne_unit (scalar : Target) : ATarget.ofScalar scalar ≠ .unit := by
  cases scalar <;> simp [ATarget.ofScalar]

/-- The zero value printed for an `if` or `case` result. -/
def azero : ATarget → Expr
  | .bool => .bool false
  | .wordPair => .tuple (.number 0) (.number 0)
  | .wordSum => .inl (.number 0)
  | _ => .number 0

/-- The renderer's spelling of the zero values. -/
def azeroText : ATarget → String
  | .word => "0"
  | .bool => "false"
  | .unit => ""
  | .wordPair => "(0, 0)"
  | .wordSum => "inl(0)"

theorem azero_print {target : ATarget} (valued : target ≠ .unit) :
    (azero target).print = azeroText target := by
  cases target
  case unit => exact absurd rfl valued
  all_goals rfl

/-- A rendered scalar operand of the call-graph helpers, as the renderer's
private `scalarValue` builds it. -/
def ascalarValue (rendered : ARendered) : Except EmitError ScalarRenderer.Rendered :=
  (AggregateRenderer.requireValue rendered).bind fun value =>
    .ok ⟨rendered.lines, value, rendered.nextId⟩

/-- A scalar operand as an aggregate rendering with a value name. -/
def ARendered.ofScalar (rendered : ScalarRenderer.Rendered) : ARendered :=
  ⟨rendered.lines, some rendered.value, rendered.nextId⟩

/-- The statements printed for a projection: a zero result, then a pair match
whose case assigns the picked component. -/
def projectionStmts (next : Nat) (value : String) (picked : Nat) : List Stmt :=
  [.letDecl (temporary next) .word (.number 0),
    .matchPair (.name value) (payloadTemp (next + 1)) (payloadTemp (next + 2))
      [.assign (temporary next) (.name (payloadTemp picked))]]

theorem arequireValue_ok {rendered : ARendered} {value : String}
    (equation : AggregateRenderer.requireValue rendered = .ok value) :
    rendered.value = some value := by
  unfold AggregateRenderer.requireValue at equation
  cases found : rendered.value with
  | none =>
      rw [found] at equation
      cases equation
  | some value' =>
      rw [found] at equation
      cases equation
      rfl

theorem ascalarValue_ok {rendered : ARendered} {value : ScalarRenderer.Rendered}
    (equation : ascalarValue rendered = .ok value) :
    rendered.value = some value.value ∧ ARendered.ofScalar value = rendered := by
  unfold ascalarValue at equation
  obtain ⟨name, nameEquation, equation⟩ := except_bind_eq_ok equation
  cases equation
  have found := arequireValue_ok nameEquation
  refine ⟨found, ?_⟩
  obtain ⟨lines, value, next⟩ := rendered
  simp only at found
  subst found
  rfl

namespace AggregateEquations

variable {functions : List String} {target : ATarget} {bindings : List Binding}
  {indent first : Nat} {rendered : ARendered}

theorem word (value : Solcore.Core.Word) :
    AggregateRenderer.render functions target bindings indent first (.word value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .word (.number value.val)),
        some (temporary first), first + 1⟩ := by
  simp only [AggregateRenderer.render]
  rfl

theorem bool (value : Bool) :
    AggregateRenderer.render functions target bindings indent first (.bool value) =
      .ok ⟨Stmt.lines indent (.letDecl (temporary first) .bool (.bool value)),
        some (temporary first), first + 1⟩ := by
  simp only [AggregateRenderer.render]
  rfl

theorem unit :
    AggregateRenderer.render functions target bindings indent first .unit =
      .ok ⟨[], none, first⟩ := by
  simp only [AggregateRenderer.render]

theorem var_ok {index : Nat}
    (equation : AggregateRenderer.render functions target bindings indent first (.var index) =
      .ok rendered) :
    (∃ (name : String) (kind : ATarget), kind ≠ .unit ∧
        bindings[index]? = some (valueBinding kind name) ∧ rendered = ⟨[], some name, first⟩) ∨
      (bindings[index]? = some Binding.unit ∧ rendered = ⟨[], none, first⟩) := by
  simp only [AggregateRenderer.render] at equation
  cases found : bindings[index]? with
  | none =>
      rw [found] at equation
      cases equation
  | some binding =>
      rw [found] at equation
      cases binding with
      | word name =>
          exact Or.inl ⟨name, .word, by simp, rfl, (Except.ok.inj equation).symm⟩
      | bool name =>
          exact Or.inl ⟨name, .bool, by simp, rfl, (Except.ok.inj equation).symm⟩
      | wordPair name =>
          exact Or.inl ⟨name, .wordPair, by simp, rfl, (Except.ok.inj equation).symm⟩
      | wordSum name =>
          exact Or.inl ⟨name, .wordSum, by simp, rfl, (Except.ok.inj equation).symm⟩
      | unit => exact Or.inr ⟨rfl, (Except.ok.inj equation).symm⟩
      | cellWord name => cases equation

theorem newCellLet_ok {initializer body : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.letE (.newCell .word initializer) body) = .ok rendered) :
    ∃ initial value rest,
      AggregateRenderer.render functions .word bindings indent first initializer = .ok initial ∧
      initial.value = some value ∧
      AggregateRenderer.render functions target
        (.cellWord (cellTemp initial.nextId) :: bindings) indent (initial.nextId + 1) body =
          .ok rest ∧
      rendered = ⟨initial.lines ++
        Stmt.lines indent (.letDecl (cellTemp initial.nextId) .word (.name value)) ++ rest.lines,
        rest.value, rest.nextId⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  refine ⟨initial, value, rest, initialEquation, arequireValue_ok valueEquation, restEquation, ?_⟩
  rw [← cellDecl_lines]
  exact (Except.ok.inj equation).symm

theorem letE_infer {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ kind, infer? (bindings.map Binding.kind) functions.length initializer = some kind := by
  rw [AggregateRenderer.render.eq_6 _ _ _ _ _ _ _ notCell] at equation
  cases inferred : infer? (bindings.map Binding.kind) functions.length initializer with
  | none =>
      rw [inferred] at equation
      cases equation
  | some kind => exact ⟨kind, rfl⟩

theorem letE_unit_ok {initializer body : CoreExpr}
    (notCell : ∀ inner, initializer = .newCell .word inner → False)
    (inferred : infer? (bindings.map Binding.kind) functions.length initializer = some .unit)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ initial rest,
      AggregateRenderer.render functions .unit bindings indent first initializer = .ok initial ∧
      AggregateRenderer.render functions target (.unit :: bindings) indent initial.nextId body =
        .ok rest ∧
      rendered = ⟨initial.lines ++ rest.lines, rest.value, rest.nextId⟩ := by
  rw [AggregateRenderer.render.eq_6 _ _ _ _ _ _ _ notCell, inferred] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨initial, rest, initialEquation, restEquation, (Except.ok.inj equation).symm⟩

theorem letE_value_ok {initializer body : CoreExpr} {kind : ATarget}
    (notCell : ∀ inner, initializer = .newCell .word inner → False) (valued : kind ≠ .unit)
    (inferred : infer? (bindings.map Binding.kind) functions.length initializer = some kind)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.letE initializer body) = .ok rendered) :
    ∃ initial value rest,
      AggregateRenderer.render functions kind bindings indent first initializer = .ok initial ∧
      initial.value = some value ∧
      AggregateRenderer.render functions target
        (valueBinding kind (temporary initial.nextId) :: bindings) indent (initial.nextId + 1)
          body = .ok rest ∧
      rendered = ⟨initial.lines ++
        Stmt.lines indent (.letDecl (temporary initial.nextId) kind.localType (.name value)) ++
        rest.lines, rest.value, rest.nextId⟩ := by
  rw [AggregateRenderer.render.eq_6 _ _ _ _ _ _ _ notCell, inferred] at equation
  obtain ⟨initial, initialEquation, equation⟩ := except_bind_eq_ok equation
  cases kind
  case unit => exact absurd rfl valued
  all_goals
    obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨rest, restEquation, equation⟩ := except_bind_eq_ok equation
    exact ⟨initial, value, rest, initialEquation, arequireValue_ok valueEquation, restEquation,
      (Except.ok.inj equation).symm⟩

theorem ifE_unit_ok {condition yes no : CoreExpr}
    (equation : AggregateRenderer.render functions .unit bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested conditionValue selected fallback,
      AggregateRenderer.render functions .bool bindings indent first condition = .ok tested ∧
      tested.value = some conditionValue ∧
      AggregateRenderer.render functions .unit bindings (indent + 4) tested.nextId yes =
        .ok selected ∧
      AggregateRenderer.render functions .unit bindings (indent + 4) selected.nextId no =
        .ok fallback ∧
      rendered = ⟨tested.lines ++ [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++
        selected.lines ++ [indentLine indent "} else {"] ++ fallback.lines ++
        [indentLine indent "}"], none, fallback.nextId⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨conditionValue, conditionEquation, equation⟩ := except_bind_eq_ok equation
  have unitTest : ((.unit : ATarget) == .unit) = true := rfl
  rw [if_pos unitTest] at equation
  obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨tested, conditionValue, selected, fallback, testedEquation,
    arequireValue_ok conditionEquation, selectedEquation, fallbackEquation,
    (Except.ok.inj equation).symm⟩

theorem ifE_value_ok {condition yes no : CoreExpr} (valued : target ≠ .unit)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.ifE condition yes no) = .ok rendered) :
    ∃ tested conditionValue selected selectedValue fallback fallbackValue,
      AggregateRenderer.render functions .bool bindings indent first condition = .ok tested ∧
      tested.value = some conditionValue ∧
      AggregateRenderer.render functions target bindings (indent + 4) (tested.nextId + 1) yes =
        .ok selected ∧
      selected.value = some selectedValue ∧
      AggregateRenderer.render functions target bindings (indent + 4) selected.nextId no =
        .ok fallback ∧
      fallback.value = some fallbackValue ∧
      rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("if (" ++ conditionValue ++ ") {")] ++ selected.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";"),
            indentLine indent "} else {"] ++
          fallback.lines ++
          [indentLine (indent + 4) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";"),
            indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  cases target
  case unit => exact absurd rfl valued
  all_goals
    simp only [AggregateRenderer.render] at equation
    obtain ⟨tested, testedEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨conditionValue, conditionEquation, equation⟩ := except_bind_eq_ok equation
    rw [if_neg (by decide)] at equation
    obtain ⟨resultValue, resultEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨selected, selectedEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨selectedValue, selectedValueEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨fallback, fallbackEquation, equation⟩ := except_bind_eq_ok equation
    obtain ⟨fallbackValue, fallbackValueEquation, equation⟩ := except_bind_eq_ok equation
    have resultName : resultValue = temporary tested.nextId :=
      (Option.some.inj (arequireValue_ok resultEquation)).symm
    subst resultName
    exact ⟨tested, conditionValue, selected, selectedValue, fallback, fallbackValue,
      testedEquation, arequireValue_ok conditionEquation, selectedEquation,
      arequireValue_ok selectedValueEquation, fallbackEquation,
      arequireValue_ok fallbackValueEquation, (Except.ok.inj equation).symm⟩

theorem pair_ok {left right : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.pair left right) = .ok rendered) :
    ∃ leftRendered leftValue rightRendered rightValue,
      AggregateRenderer.render functions .word bindings indent first left = .ok leftRendered ∧
      leftRendered.value = some leftValue ∧
      AggregateRenderer.render functions .word bindings indent leftRendered.nextId right =
        .ok rightRendered ∧
      rightRendered.value = some rightValue ∧
      rendered = ⟨leftRendered.lines ++ rightRendered.lines ++
          Stmt.lines indent (.letDecl (temporary rightRendered.nextId) .wordPair
            (.tuple (.name leftValue) (.name rightValue))),
        some (temporary rightRendered.nextId), rightRendered.nextId + 1⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨leftRendered, leftEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨leftValue, leftValueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightRendered, rightEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨rightValue, rightValueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨leftRendered, leftValue, rightRendered, rightValue, leftEquation,
    arequireValue_ok leftValueEquation, rightEquation, arequireValue_ok rightValueEquation,
    (Except.ok.inj equation).symm⟩

theorem first_ok {operand : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.first operand) = .ok rendered) :
    ∃ operandRendered value,
      AggregateRenderer.render functions .wordPair bindings indent first operand =
        .ok operandRendered ∧
      operandRendered.value = some value ∧
      rendered = ⟨operandRendered.lines ++ Stmt.listLines indent
          (projectionStmts operandRendered.nextId value (operandRendered.nextId + 1)),
        some (temporary operandRendered.nextId), operandRendered.nextId + 3⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨operandRendered, operandEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨resultValue, resultEquation, equation⟩ := except_bind_eq_ok equation
  have resultName : resultValue = temporary operandRendered.nextId :=
    (Option.some.inj (arequireValue_ok resultEquation)).symm
  subst resultName
  refine ⟨operandRendered, value, operandEquation, arequireValue_ok valueEquation, ?_⟩
  rw [← (Except.ok.inj equation)]
  simp only [List.append_assoc]
  rfl

theorem second_ok {operand : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.second operand) = .ok rendered) :
    ∃ operandRendered value,
      AggregateRenderer.render functions .wordPair bindings indent first operand =
        .ok operandRendered ∧
      operandRendered.value = some value ∧
      rendered = ⟨operandRendered.lines ++ Stmt.listLines indent
          (projectionStmts operandRendered.nextId value (operandRendered.nextId + 2)),
        some (temporary operandRendered.nextId), operandRendered.nextId + 3⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨operandRendered, operandEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨resultValue, resultEquation, equation⟩ := except_bind_eq_ok equation
  have resultName : resultValue = temporary operandRendered.nextId :=
    (Option.some.inj (arequireValue_ok resultEquation)).symm
  subst resultName
  refine ⟨operandRendered, value, operandEquation, arequireValue_ok valueEquation, ?_⟩
  rw [← (Except.ok.inj equation)]
  simp only [List.append_assoc]
  rfl

theorem inLeft_ok {payload : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.inLeft .word payload) = .ok rendered) :
    ∃ payloadRendered value,
      AggregateRenderer.render functions .word bindings indent first payload =
        .ok payloadRendered ∧
      payloadRendered.value = some value ∧
      rendered = ⟨payloadRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary payloadRendered.nextId) .wordSum (.inl (.name value))),
        some (temporary payloadRendered.nextId), payloadRendered.nextId + 1⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨payloadRendered, payloadEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨payloadRendered, value, payloadEquation, arequireValue_ok valueEquation,
    (Except.ok.inj equation).symm⟩

theorem inRight_ok {payload : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.inRight .word payload) = .ok rendered) :
    ∃ payloadRendered value,
      AggregateRenderer.render functions .word bindings indent first payload =
        .ok payloadRendered ∧
      payloadRendered.value = some value ∧
      rendered = ⟨payloadRendered.lines ++ Stmt.lines indent
          (.letDecl (temporary payloadRendered.nextId) .wordSum (.inr (.name value))),
        some (temporary payloadRendered.nextId), payloadRendered.nextId + 1⟩ := by
  simp only [AggregateRenderer.render] at equation
  obtain ⟨payloadRendered, payloadEquation, equation⟩ := except_bind_eq_ok equation
  obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
  exact ⟨payloadRendered, value, payloadEquation, arequireValue_ok valueEquation,
    (Except.ok.inj equation).symm⟩

theorem caseE_unit_ok {scrutinee yes no : CoreExpr}
    (equation : AggregateRenderer.render functions .unit bindings indent first
      (.caseE scrutinee yes no) = .ok rendered) :
    ∃ tested value selected fallback,
      AggregateRenderer.render functions .wordSum bindings indent first scrutinee =
        .ok tested ∧
      tested.value = some value ∧
      AggregateRenderer.render functions .unit (.word (payloadTemp tested.nextId) :: bindings)
        (indent + 8) (tested.nextId + 1) yes = .ok selected ∧
      AggregateRenderer.render functions .unit (.word (payloadTemp selected.nextId) :: bindings)
        (indent + 8) (selected.nextId + 1) no = .ok fallback ∧
      rendered = ⟨tested.lines ++
          [indentLine indent ("match (" ++ value ++ ") {"),
            indentLine (indent + 4) ("case inl(" ++ payloadTemp tested.nextId ++ ") {")] ++
          selected.lines ++
          [indentLine (indent + 4) "}",
            indentLine (indent + 4) ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
          fallback.lines ++ [indentLine (indent + 4) "}", indentLine indent "}"],
        none, fallback.nextId⟩ := by
  have unfolded : ((AggregateRenderer.render functions .wordSum bindings indent first
      scrutinee).bind fun tested => (AggregateRenderer.requireValue tested).bind fun value =>
        (AggregateRenderer.render functions .unit (.word (payloadTemp tested.nextId) :: bindings)
          (indent + 8) (tested.nextId + 1) yes).bind fun selected =>
          (AggregateRenderer.render functions .unit
            (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
              no).bind fun fallback =>
            (Except.ok selected.lines : Except EmitError (List String)).bind fun selectedLines =>
              (Except.ok fallback.lines : Except EmitError (List String)).bind
                fun fallbackLines => Except.ok (⟨tested.lines ++ [] ++
                  [indentLine indent ("match (" ++ value ++ ") {"),
                    indentLine (indent + 4) ("case inl(" ++ payloadTemp tested.nextId ++ ") {")] ++
                  selectedLines ++
                  [indentLine (indent + 4) "}",
                    indentLine (indent + 4)
                      ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
                  fallbackLines ++ [indentLine (indent + 4) "}", indentLine indent "}"],
                  none, fallback.nextId⟩ : ARendered)) = .ok rendered := by
    rw [← equation]
    simp only [AggregateRenderer.render]
    rfl
  obtain ⟨tested, testedEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨value, valueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selected, selectedEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallback, fallbackEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selectedLines, selectedLinesEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallbackLines, fallbackLinesEquation, unfolded⟩ := except_bind_eq_ok unfolded
  cases selectedLinesEquation
  cases fallbackLinesEquation
  refine ⟨tested, value, selected, fallback, testedEquation, arequireValue_ok valueEquation,
    selectedEquation, fallbackEquation, ?_⟩
  rw [← (Except.ok.inj unfolded), List.append_nil]

theorem caseE_value_ok {scrutinee yes no : CoreExpr} (valued : target ≠ .unit)
    (equation : AggregateRenderer.render functions target bindings indent first
      (.caseE scrutinee yes no) = .ok rendered) :
    ∃ tested value selected selectedValue fallback fallbackValue,
      AggregateRenderer.render functions .wordSum bindings indent first scrutinee =
        .ok tested ∧
      tested.value = some value ∧
      AggregateRenderer.render functions target
        (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8) (tested.nextId + 2)
          yes = .ok selected ∧
      selected.value = some selectedValue ∧
      AggregateRenderer.render functions target
        (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
          no = .ok fallback ∧
      fallback.value = some fallbackValue ∧
      rendered = ⟨tested.lines ++
          [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
            target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
          [indentLine indent ("match (" ++ value ++ ") {"),
            indentLine (indent + 4) ("case inl(" ++ payloadTemp (tested.nextId + 1) ++ ") {")] ++
          (selected.lines ++
            [indentLine (indent + 8) (temporary tested.nextId ++ " = " ++ selectedValue ++ ";")]) ++
          [indentLine (indent + 4) "}",
            indentLine (indent + 4) ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
          (fallback.lines ++
            [indentLine (indent + 8) (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";")]) ++
          [indentLine (indent + 4) "}", indentLine indent "}"],
        some (temporary tested.nextId), fallback.nextId⟩ := by
  have unfolded : ((AggregateRenderer.render functions .wordSum bindings indent first
      scrutinee).bind fun tested => (AggregateRenderer.requireValue tested).bind fun value =>
        (AggregateRenderer.render functions target
          (.word (payloadTemp (tested.nextId + 1)) :: bindings) (indent + 8)
            (tested.nextId + 2) yes).bind fun selected =>
          (AggregateRenderer.render functions target
            (.word (payloadTemp selected.nextId) :: bindings) (indent + 8) (selected.nextId + 1)
              no).bind fun fallback =>
            (AggregateRenderer.requireValue selected).bind fun selectedValue =>
              (Except.ok (selected.lines ++ [indentLine (indent + 8)
                (temporary tested.nextId ++ " = " ++ selectedValue ++ ";")]) :
                  Except EmitError (List String)).bind fun selectedLines =>
              (AggregateRenderer.requireValue fallback).bind fun fallbackValue =>
                (Except.ok (fallback.lines ++ [indentLine (indent + 8)
                  (temporary tested.nextId ++ " = " ++ fallbackValue ++ ";")]) :
                    Except EmitError (List String)).bind fun fallbackLines =>
                Except.ok (⟨tested.lines ++
                  [indentLine indent ("let " ++ temporary tested.nextId ++ ": " ++
                    target.localType.spelling ++ " = " ++ azeroText target ++ ";")] ++
                  [indentLine indent ("match (" ++ value ++ ") {"),
                    indentLine (indent + 4)
                      ("case inl(" ++ payloadTemp (tested.nextId + 1) ++ ") {")] ++
                  selectedLines ++
                  [indentLine (indent + 4) "}",
                    indentLine (indent + 4)
                      ("case inr(" ++ payloadTemp selected.nextId ++ ") {")] ++
                  fallbackLines ++ [indentLine (indent + 4) "}", indentLine indent "}"],
                  some (temporary tested.nextId), fallback.nextId⟩ : ARendered)) =
        .ok rendered := by
    rw [← equation]
    cases target
    case unit => exact absurd rfl valued
    all_goals
      simp only [AggregateRenderer.render]
      rfl
  obtain ⟨tested, testedEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨value, valueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selected, selectedEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallback, fallbackEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selectedValue, selectedValueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨selectedLines, selectedLinesEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallbackValue, fallbackValueEquation, unfolded⟩ := except_bind_eq_ok unfolded
  obtain ⟨fallbackLines, fallbackLinesEquation, unfolded⟩ := except_bind_eq_ok unfolded
  cases selectedLinesEquation
  cases fallbackLinesEquation
  exact ⟨tested, value, selected, selectedValue, fallback, fallbackValue, testedEquation,
    arequireValue_ok valueEquation, selectedEquation, arequireValue_ok selectedValueEquation,
    fallbackEquation, arequireValue_ok fallbackValueEquation, (Except.ok.inj unfolded).symm⟩

theorem loadCell_ok {index : Nat}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.loadCell (.var index)) = .ok rendered) :
    ∃ name, bindings[index]? = some (Binding.cellWord name) ∧
      rendered = ⟨Stmt.lines indent (.letDecl (temporary first) .word (.name name)),
        some (temporary first), first + 1⟩ := by
  have unfolded : ((match bindings[index]? with
      | some (Binding.cellWord name) => (Except.ok name : Except EmitError String)
      | _ => .error (.unsupportedExpression "cell reference is not a direct private local")).bind
        fun name => Except.ok (⟨Stmt.lines indent (.letDecl (temporary first) .word (.name name)),
          some (temporary first), first + 1⟩ : ARendered)) = .ok rendered := equation
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
      | wordPair name => cases unfolded
      | wordSum name => cases unfolded

theorem storeCell_ok {index : Nat} {value : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.storeCell (.var index) value) = .ok rendered) :
    ∃ name written result, bindings[index]? = some (Binding.cellWord name) ∧
      AggregateRenderer.render functions .word bindings indent first value = .ok written ∧
      written.value = some result ∧
      rendered = ⟨written.lines ++ Stmt.lines indent (.assign name (.name result)), none,
        written.nextId⟩ := by
  have unfolded : ((match bindings[index]? with
      | some (Binding.cellWord name) => (Except.ok name : Except EmitError String)
      | _ => .error (.unsupportedExpression "cell reference is not a direct private local")).bind
        fun name => (AggregateRenderer.render functions .word bindings indent first value).bind
          fun written => (AggregateRenderer.requireValue written).bind fun result =>
            Except.ok (⟨written.lines ++ Stmt.lines indent (.assign name (.name result)), none,
              written.nextId⟩ : ARendered)) = .ok rendered := equation
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
          exact ⟨name, written, result, rfl, writtenEquation, arequireValue_ok resultEquation,
            (Except.ok.inj unfolded).symm⟩
      | word name => cases unfolded
      | bool name => cases unfolded
      | unit => cases unfolded
      | wordPair name => cases unfolded
      | wordSum name => cases unfolded

/-- `!` and `~` bind their result to a fresh temporary. -/
theorem unary (scalar : Target) (op : Solcore.Core.Wire.UnaryOp) (sourceOp : UnaryOp)
    (operand : CoreExpr) (selected : sourceUnary? op = some sourceOp) :
    AggregateRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.unary op operand) =
      (AggregateRenderer.render functions (if op == .boolNot then .bool else .word) bindings
        indent first operand).bind fun operandRendered =>
        (ascalarValue operandRendered).bind fun value =>
          .ok ⟨value.lines ++ Stmt.lines indent (.letDecl (temporary value.nextId)
              (LocalType.ofTarget scalar) (.unary sourceOp (.name value.value))),
            some (temporary value.nextId), value.nextId + 1⟩ := by
  cases op <;> simp only [sourceUnary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateRenderer.render] <;> rfl

/-- `CLZ` snapshots its operand, then calls the raw opcode alias. -/
theorem clz (operand : CoreExpr) :
    AggregateRenderer.render functions .word bindings indent first (.unary .wordClz operand) =
      (AggregateRenderer.render functions .word bindings indent first operand).bind
        fun operandRendered => (ascalarValue operandRendered).bind fun value =>
          .ok ⟨(snapshotOf indent value).lines ++ Stmt.lines indent
              (.letDecl (temporary (value.nextId + 1)) .word
                (.call1 "sc_clz" (.name (temporary value.nextId)))),
            some (temporary (value.nextId + 1)), value.nextId + 2⟩ := by
  simp only [AggregateRenderer.render]
  rfl

/-- The infix operations bind their result to a fresh temporary. -/
theorem binary (scalar : Target) (op : Solcore.Core.Wire.BinaryOp) (sourceOp : BinaryOp)
    (left right : CoreExpr) (selected : sourceBinary? op = some sourceOp) :
    AggregateRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.binary op left right) =
      (AggregateRenderer.render functions .word bindings indent first left).bind
        fun leftRendered => (ascalarValue leftRendered).bind fun leftValue =>
          (AggregateRenderer.render functions .word bindings indent leftValue.nextId right).bind
            fun rightRendered => (ascalarValue rightRendered).bind fun rightValue =>
              .ok ⟨leftValue.lines ++ rightValue.lines ++ Stmt.lines indent
                  (.letDecl (temporary rightValue.nextId) (LocalType.ofTarget scalar)
                    (.binary sourceOp (.name leftValue.value) (.name rightValue.value))),
                some (temporary rightValue.nextId), rightValue.nextId + 1⟩ := by
  cases op <;> simp only [sourceBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateRenderer.render] <;> rfl

/-- Extended binary operations snapshot both operands, left to right, then
call the raw opcode alias. -/
theorem binary_primitive (scalar : Target) (op : Solcore.Core.Wire.BinaryOp)
    (build : String → String → Expr) (left right : CoreExpr)
    (selected : primitiveBinary? op = some build) :
    AggregateRenderer.render functions (ATarget.ofScalar scalar) bindings indent first
        (.binary op left right) =
      (AggregateRenderer.render functions .word bindings indent first left).bind
        fun leftRendered => (ascalarValue leftRendered).bind fun leftValue =>
          (AggregateRenderer.render functions .word bindings indent (leftValue.nextId + 1)
            right).bind fun rightRendered => (ascalarValue rightRendered).bind fun rightValue =>
              .ok ⟨(snapshotOf indent leftValue).lines ++ (snapshotOf indent rightValue).lines ++
                  Stmt.lines indent (.letDecl (temporary (rightValue.nextId + 1))
                    (LocalType.ofTarget scalar)
                    (build (temporary leftValue.nextId) (temporary rightValue.nextId))),
                some (temporary (rightValue.nextId + 1)), rightValue.nextId + 2⟩ := by
  cases op <;> simp only [primitiveBinary?, reduceCtorEq, Option.some.injEq] at selected <;>
    subst selected <;> cases scalar <;> simp only [AggregateRenderer.render] <;> rfl

/-- `ADDMOD` and `MULMOD` snapshot all three operands, then call the raw
opcode alias. -/
theorem ternary (op : Solcore.Core.Wire.TernaryOp) (one two three : CoreExpr) :
    AggregateRenderer.render functions .word bindings indent first (.ternary op one two three) =
      (AggregateRenderer.render functions .word bindings indent first one).bind
        fun oneRendered => (ascalarValue oneRendered).bind fun oneValue =>
          (AggregateRenderer.render functions .word bindings indent (oneValue.nextId + 1)
            two).bind fun twoRendered => (ascalarValue twoRendered).bind fun twoValue =>
              (AggregateRenderer.render functions .word bindings indent (twoValue.nextId + 1)
                three).bind fun threeRendered => (ascalarValue threeRendered).bind
                  fun threeValue =>
                    .ok ⟨(snapshotOf indent oneValue).lines ++
                        (snapshotOf indent twoValue).lines ++
                        (snapshotOf indent threeValue).lines ++
                        Stmt.lines indent (.letDecl (temporary (threeValue.nextId + 1)) .word
                          (.call3 (ternaryCallee op) (.name (temporary oneValue.nextId))
                            (.name (temporary twoValue.nextId))
                            (.name (temporary threeValue.nextId)))),
                      some (temporary (threeValue.nextId + 1)), threeValue.nextId + 2⟩ := by
  simp only [AggregateRenderer.render]
  cases op <;> rfl

theorem apply_ok {index : Nat} {argument : CoreExpr}
    (equation : AggregateRenderer.render functions target bindings indent first
      (.apply (.var index) argument) = .ok rendered) :
    bindings.length ≤ index ∧ ∃ callee argumentRendered value,
      functions[index - bindings.length]? = some callee ∧
      AggregateRenderer.render functions .word bindings indent first argument =
        .ok argumentRendered ∧
      argumentRendered.value = some value ∧
      rendered = ⟨argumentRendered.lines ++ Stmt.lines indent (.letDecl
          (temporary argumentRendered.nextId) .word (.call1 callee (.name value))),
        some (temporary argumentRendered.nextId), argumentRendered.nextId + 1⟩ := by
  by_cases below : index < bindings.length
  · dsimp only [AggregateRenderer.render] at equation
    rw [if_pos below] at equation
    cases equation
  · cases found : functions[index - bindings.length]? with
    | none =>
        dsimp only [AggregateRenderer.render] at equation
        rw [if_neg below, found] at equation
        cases equation
    | some callee =>
        dsimp only [AggregateRenderer.render] at equation
        rw [if_neg below, found] at equation
        obtain ⟨argumentRendered, argumentEquation, equation⟩ := except_bind_eq_ok equation
        obtain ⟨value, valueEquation, equation⟩ := except_bind_eq_ok equation
        exact ⟨Nat.le_of_not_lt below, callee, argumentRendered, value, rfl, argumentEquation,
          arequireValue_ok valueEquation, (Except.ok.inj equation).symm⟩

end AggregateEquations

namespace AggregateKinds

theorem local_beq (first second : Local) : (first == second) = decide (first = second) := by
  cases first <;> cases second <;> rfl

theorem infer_toLocal {locals : List Local} {prior : Nat} {expression : CoreExpr}
    {kind : ATarget} (inferred : infer? locals prior expression = some kind) :
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
    {kind : ATarget} (inferred : initializerKind? locals prior expression = some kind.toLocal) :
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

theorem pair {locals : List Local} {prior : Nat} {left right : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.pair left right) = some result) :
    initializerKind? locals prior left = some .word ∧
      initializerKind? locals prior right = some .word ∧ result = .wordPair := by
  have unfolded : ((initializerKind? locals prior left).bind fun found =>
      (if found == Local.word then some () else none).bind fun _ =>
        (initializerKind? locals prior right).bind fun found' =>
          (if found' == Local.word then some () else none).bind fun _ => some Local.wordPair) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, leftKind, checked, check, found', rightKind, checked', check', last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases found' <;> simp [local_beq] at check'
  cases last
  exact ⟨leftKind, rightKind, rfl⟩

theorem first {locals : List Local} {prior : Nat} {operand : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.first operand) = some result) :
    initializerKind? locals prior operand = some .wordPair ∧ result = .word := by
  have unfolded : ((initializerKind? locals prior operand).bind fun found =>
      (if found == Local.wordPair then some () else none).bind fun _ => some Local.word) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, operandKind, checked, check, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases last
  exact ⟨operandKind, rfl⟩

theorem second {locals : List Local} {prior : Nat} {operand : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.second operand) = some result) :
    initializerKind? locals prior operand = some .wordPair ∧ result = .word := by
  have unfolded : ((initializerKind? locals prior operand).bind fun found =>
      (if found == Local.wordPair then some () else none).bind fun _ => some Local.word) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, operandKind, checked, check, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases last
  exact ⟨operandKind, rfl⟩

theorem inLeft {locals : List Local} {prior : Nat} {type : Solcore.Core.Wire.Ty}
    {payload : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.inLeft type payload) = some result) :
    type = .word ∧ initializerKind? locals prior payload = some .word ∧ result = .wordSum := by
  cases type
  case word =>
    have unfolded : ((initializerKind? locals prior payload).bind fun found =>
        (if found == Local.word then some () else none).bind fun _ => some Local.wordSum) =
        some result := inferred
    simp only [Option.bind_eq_some_iff] at unfolded
    obtain ⟨found, payloadKind, checked, check, last⟩ := unfolded
    cases found <;> simp [local_beq] at check
    cases last
    exact ⟨rfl, payloadKind, rfl⟩
  all_goals cases inferred

theorem inRight {locals : List Local} {prior : Nat} {type : Solcore.Core.Wire.Ty}
    {payload : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.inRight type payload) = some result) :
    type = .word ∧ initializerKind? locals prior payload = some .word ∧ result = .wordSum := by
  cases type
  case word =>
    have unfolded : ((initializerKind? locals prior payload).bind fun found =>
        (if found == Local.word then some () else none).bind fun _ => some Local.wordSum) =
        some result := inferred
    simp only [Option.bind_eq_some_iff] at unfolded
    obtain ⟨found, payloadKind, checked, check, last⟩ := unfolded
    cases found <;> simp [local_beq] at check
    cases last
    exact ⟨rfl, payloadKind, rfl⟩
  all_goals cases inferred

theorem caseE {locals : List Local} {prior : Nat} {scrutinee yes no : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.caseE scrutinee yes no) = some result) :
    initializerKind? locals prior scrutinee = some .wordSum ∧
      initializerKind? (.word :: locals) prior yes = some result ∧
      initializerKind? (.word :: locals) prior no = some result ∧ result ≠ .cellWord := by
  have unfolded : ((initializerKind? locals prior scrutinee).bind fun found =>
      (if found == Local.wordSum then some () else none).bind fun _ =>
        (initializerKind? (.word :: locals) prior yes).bind fun left =>
          (initializerKind? (.word :: locals) prior no).bind fun right =>
            if (left == right && left != Local.cellWord) = true then some left else none) =
      some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, scrutineeKind, checked, check, left, yesKind, right, noKind, last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases left <;> cases right <;> simp [local_beq, bne] at last <;> subst last <;>
    exact ⟨scrutineeKind, yesKind, noKind, by simp⟩

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

/-- The local kind of a scalar result. -/
def scalarKind : Target → Local
  | .word => .word
  | .bool => .bool

theorem unary_eq (locals : List Local) (prior : Nat) (op : Solcore.Core.Wire.UnaryOp)
    (operand : CoreExpr) :
    initializerKind? locals prior (.unary op operand) =
      if MutationKinds.integerUnary op then none else
        (initializerKind? locals prior operand).bind fun found =>
          (if found == scalarKind (Target.unaryOperand op) then some () else none).bind fun _ =>
            some (scalarKind (Target.unaryResult op)) := by
  cases op <;> rfl

theorem binary_eq (locals : List Local) (prior : Nat) (op : Solcore.Core.Wire.BinaryOp)
    (left right : CoreExpr) :
    initializerKind? locals prior (.binary op left right) =
      if MutationKinds.integerBinary op then none else
        (initializerKind? locals prior left).bind fun found =>
          (if found == Local.word then some () else none).bind fun _ =>
            (initializerKind? locals prior right).bind fun found' =>
              (if found' == Local.word then some () else none).bind fun _ =>
                some (scalarKind (Target.binaryResult op)) := by
  cases op <;> rfl

theorem unary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.UnaryOp}
    {operand : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.unary op operand) = some result) :
    MutationKinds.integerUnary op = false ∧
      initializerKind? locals prior operand = some (scalarKind (Target.unaryOperand op)) ∧
      result = scalarKind (Target.unaryResult op) := by
  rw [unary_eq] at inferred
  cases integer : MutationKinds.integerUnary op
  · rw [integer, if_neg (by simp)] at inferred
    simp only [Option.bind_eq_some_iff] at inferred
    obtain ⟨found, operandKind, checked, check, last⟩ := inferred
    have same : found = scalarKind (Target.unaryOperand op) := by
      by_cases same : found = scalarKind (Target.unaryOperand op)
      · exact same
      · rw [local_beq, decide_eq_false same] at check
        cases check
    cases last
    exact ⟨rfl, same ▸ operandKind, rfl⟩
  · rw [integer, if_pos rfl] at inferred
    cases inferred

theorem binary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.BinaryOp}
    {left right : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.binary op left right) = some result) :
    MutationKinds.integerBinary op = false ∧
      initializerKind? locals prior left = some .word ∧
      initializerKind? locals prior right = some .word ∧
      result = scalarKind (Target.binaryResult op) := by
  rw [binary_eq] at inferred
  cases integer : MutationKinds.integerBinary op
  · rw [integer, if_neg (by simp)] at inferred
    simp only [Option.bind_eq_some_iff] at inferred
    obtain ⟨found, leftKind, checked, check, found', rightKind, checked', check', last⟩ :=
      inferred
    cases found <;> simp [local_beq] at check
    cases found' <;> simp [local_beq] at check'
    cases last
    exact ⟨rfl, leftKind, rightKind, rfl⟩
  · rw [integer, if_pos rfl] at inferred
    cases inferred

theorem ternary {locals : List Local} {prior : Nat} {op : Solcore.Core.Wire.TernaryOp}
    {one two three : CoreExpr} {result : Local}
    (inferred : initializerKind? locals prior (.ternary op one two three) = some result) :
    initializerKind? locals prior one = some .word ∧
      initializerKind? locals prior two = some .word ∧
      initializerKind? locals prior three = some .word ∧ result = .word := by
  have unfolded : ((initializerKind? locals prior one).bind fun found =>
      (if found == Local.word then some () else none).bind fun _ =>
        (initializerKind? locals prior two).bind fun found' =>
          (if found' == Local.word then some () else none).bind fun _ =>
            (initializerKind? locals prior three).bind fun found'' =>
              (if found'' == Local.word then some () else none).bind fun _ =>
                some Local.word) = some result := inferred
  simp only [Option.bind_eq_some_iff] at unfolded
  obtain ⟨found, oneKind, checked, check, found', twoKind, checked', check', found'', threeKind,
    checked'', check'', last⟩ := unfolded
  cases found <;> simp [local_beq] at check
  cases found' <;> simp [local_beq] at check'
  cases found'' <;> simp [local_beq] at check''
  cases last
  exact ⟨oneKind, twoKind, threeKind, rfl⟩

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

end AggregateKinds

end Solcore.Synthesis.Source.ScalarMeaning
