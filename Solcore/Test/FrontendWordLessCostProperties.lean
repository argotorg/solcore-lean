import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

/-! Independent exact paths for the existing ordered less-than Core expansion.
Generated lets, the weakened right reference, and every continuation are retained. -/

set_option autoImplicit false

namespace Tests.FrontendWordLessCost

open Solcore Solcore.Frontend

private def core : Core.Expr := (Core.Expr.var 1).wordLt (.var 0)
private def environment (left right : Core.Word) (tail : Core.Environment) : Core.Environment :=
  .word right :: .word left :: tail
private def result (left right : Core.Word) : Core.Value := .bool (decide (left < right))
private def firstBinding (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.letBody (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))
    (environment left right tail)], store⟩
private def secondBinding (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.letBody (.binary .wordGt (.var 0) (.var 1))
    (.word left :: environment left right tail)], store⟩
private def pending (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.binaryApply .wordGt (.word right)], store⟩
private theorem coreShape :
    core = .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1))) := by
  simp [core, Core.Expr.wordLt_expansion, Core.Expr.weakenAt]

theorem let_binding_counts_enter_and_bind_for_any_actual_value
    (value : Core.Value) (tail : Core.Environment) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 4 ⟨.eval (.letE (.var 0) (.var 0)) (value :: tail), continuation, store⟩
      ⟨.ret value, continuation, store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)

theorem exact_nested_core_keeps_left_first_and_weakens_right :
    core = .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1))) ∧
    Core.HasType [.word, .word] core .bool :=
  ⟨coreShape, Core.HasType.wordLt (.var rfl) (.var rfl)⟩

theorem ordered_variables_take_eleven_steps_under_any_continuation
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 11 ⟨.eval core (environment left right tail), continuation, store⟩
      ⟨.ret (result left right), continuation, store⟩ := by
  apply CostStepComposition.wordLt (leftCost := 1) (rightCost := 1)
  · intro frames
    exact .cons (.var rfl) .refl
  · intro frames
    simp only [Core.Expr.weakenAt, Nat.le_refl, ↓reduceIte]
    exact .cons (.var rfl) .refl

theorem all_fuel_thresholds_are_exact_and_preserve_the_actual_store
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (Core.State.initial core (environment left right tail) store) =
      .done (result left right) store ↔ 11 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (Core.State.initial core (environment left right tail) store) =
      .outOfFuel checkpoint) ↔ fuel < 11) := by
  have path := ordered_variables_take_eleven_steps_under_any_continuation left right tail store []
  exact ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff⟩

theorem actual_let_and_binary_checkpoints_retain_both_ordered_words
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) :
    Core.runStateful 2 (Core.State.initial core (environment left right tail) store) =
      .outOfFuel (firstBinding left right tail store) ∧
    Core.runStateful 5 (Core.State.initial core (environment left right tail) store) =
      .outOfFuel (secondBinding left right tail store) ∧
    Core.runStateful 10 (Core.State.initial core (environment left right tail) store) =
      .outOfFuel (pending left right store) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [coreShape] <;> rfl

theorem genuine_let_checkpoints_retain_exact_nine_and_six_step_suffixes
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (additional : Nat) :
    Core.Steps 9 (firstBinding left right tail store) (Core.State.final (result left right) store) ∧
    Core.Steps 6 (secondBinding left right tail store) (Core.State.final (result left right) store) ∧
    Core.Steps 1 (pending left right store) (Core.State.final (result left right) store) ∧
    Core.runStateful additional (firstBinding left right tail store) =
      Core.runStateful (2 + additional) (Core.State.initial core (environment left right tail) store) ∧
    Core.runStateful additional (secondBinding left right tail store) =
      Core.runStateful (5 + additional) (Core.State.initial core (environment left right tail) store) ∧
    (Core.runStateful additional (secondBinding left right tail store) =
      .done (result left right) store ↔ 6 ≤ additional) ∧
    ((∃ checkpoint, Core.runStateful additional (firstBinding left right tail store) =
      .outOfFuel checkpoint) ↔ additional < 9) := by
  have path := ordered_variables_take_eleven_steps_under_any_continuation left right tail store []
  obtain ⟨first, second, last⟩ := actual_let_and_binary_checkpoints_retain_both_ordered_words left right tail store
  exact ⟨(path.residual_of_outOfFuel first).2, (path.residual_of_outOfFuel second).2,
    (path.residual_of_outOfFuel last).2, Core.runStateful_resume first additional,
    Core.runStateful_resume second additional, path.resumed_done_iff second, path.resumed_outOfFuel_iff first⟩

theorem multichunk_resumption_uses_the_retained_let_environments
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (additional : Nat) :
    Core.runStateful 3 (firstBinding left right tail store) = .outOfFuel (secondBinding left right tail store) ∧
    Core.runStateful 5 (secondBinding left right tail store) = .outOfFuel (pending left right store) ∧
    Core.runStateful additional (pending left right store) =
      Core.runStateful (10 + additional) (Core.State.initial core (environment left right tail) store) := by
  have first := (actual_let_and_binary_checkpoints_retain_both_ordered_words left right tail store).1
  have second : Core.runStateful 3 (firstBinding left right tail store) =
      .outOfFuel (secondBinding left right tail store) := rfl
  have third : Core.runStateful 5 (secondBinding left right tail store) =
      .outOfFuel (pending left right store) := rfl
  refine ⟨second, third, ?_⟩
  simpa only [← Nat.add_assoc] using (Core.runStateful_resume third additional).trans
    ((Core.runStateful_resume second (5 + additional)).trans (Core.runStateful_resume first (3 + (5 + additional))))

theorem nonempty_continuation_is_retained_then_consumed_separately
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 11 ⟨.eval core (environment left right tail), .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (result left right), .unaryApply .boolNot :: continuation, store⟩ ∧
    Core.Steps 12 ⟨.eval core (environment left right tail), .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (.bool (!(decide (left < right)))), continuation, store⟩ := by
  have path := ordered_variables_take_eleven_steps_under_any_continuation left right tail store
    (.unaryApply .boolNot :: continuation)
  exact ⟨path, path.trans (.cons (.applyUnary rfl) .refl)⟩

theorem equal_values_do_not_remove_generated_binding_steps
    (value : Core.Word) (tail : Core.Environment) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (Core.State.initial core (environment value value tail) store) =
      .done (.bool false) store ↔ 11 ≤ fuel) ∧
    Core.runStateful 10 (Core.State.initial core (environment value value tail) store) =
      .outOfFuel (pending value value store) := by
  have threshold := (all_fuel_thresholds_are_exact_and_preserve_the_actual_store value value tail store fuel).1
  have exhausted := (actual_let_and_binary_checkpoints_retain_both_ordered_words value value tail store).2.2
  exact ⟨by simpa [result] using threshold, exhausted⟩

theorem reversing_strictly_ordered_actual_words_changes_the_boolean
    (left right : Core.Word) (ordered : left < right) (tail : Core.Environment) (store : Core.Store) :
    Core.runStateful 11 (Core.State.initial core (environment left right tail) store) = .done (.bool true) store ∧
    Core.runStateful 11 (Core.State.initial core (environment right left tail) store) = .done (.bool false) store := by
  have reversed : ¬right < left := by
    intro opposite
    exact Nat.lt_irrefl left.val (Nat.lt_trans ordered opposite)
  have first := (all_fuel_thresholds_are_exact_and_preserve_the_actual_store left right tail store 11).1.mpr (by decide)
  have second := (all_fuel_thresholds_are_exact_and_preserve_the_actual_store right left tail store 11).1.mpr (by decide)
  exact ⟨by simpa [result, ordered] using first, by simpa [result, reversed] using second⟩

end Tests.FrontendWordLessCost
