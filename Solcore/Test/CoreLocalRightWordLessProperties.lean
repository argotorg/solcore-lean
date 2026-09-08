import Solcore.Core.LocalRightWordLessTypingProperties
import Solcore.Core.LocalRightWordLessEvaluationProperties
import Solcore.Frontend.WordLessLocalRightCostProperties

/-! Independent original operand derivations exercise the local-right bridge.
The generated lets retain operand order, nested binders, exact costs and outer
continuations; raw execution uses actual words and stores without typing them. -/

set_option autoImplicit false

namespace Tests.CoreLocalRightWordLess

open Solcore Solcore.Core

private def nested : Expr := .letE (.var 1) (.letE (.var 0) (.var 0))
private def simple : Expr := (Expr.var 0).wordLt (.var 1)
private def comparison : Expr := (Expr.var 0).wordLt nested
private def environment (left right : Word) (tail : Environment) : Environment :=
  .word left :: .word right :: tail
private theorem nestedLocal : nested.LocalFragment := .letE .var (.letE .var .var)
private theorem nestedTyped (tail : Context) (definitions : DataEnvironment) :
    HasType (.word :: .word :: tail) nested .word definitions :=
  .letE (.var rfl) (.letE (.var rfl) (.var rfl))
private theorem leftEvaluates (left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment left right tail) store (.var 0) (.word left) store := .var rfl
private theorem rightEvaluates (left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment left right tail) store (.var 1) (.word right) store := .var rfl
private theorem nestedEvaluates (left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment left right tail) store nested (.word right) store :=
  .letE (.var rfl) (.letE (.var rfl) (.var rfl))
private theorem leftPath (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 1 ⟨.eval (.var 0) (environment left right tail), continuation, store⟩
      ⟨.ret (.word left), continuation, store⟩ := .cons (.var rfl) .refl
private theorem rightPath (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 1 ⟨.eval (.var 1) (environment left right tail), continuation, store⟩
      ⟨.ret (.word right), continuation, store⟩ := .cons (.var rfl) .refl
private theorem nestedPath (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 7 ⟨.eval nested (environment left right tail), continuation, store⟩
      ⟨.ret (.word right), continuation, store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet
    (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))

theorem expansion_shifts_original_right_reference_but_preserves_nested_binders
    (tail : Context) (definitions : DataEnvironment) :
    comparison = .letE (.var 0) (.letE (.letE (.var 2) (.letE (.var 0) (.var 0)))
      (.binary .wordGt (.var 0) (.var 1))) ∧ comparison.LocalFragment ∧
    HasType (.word :: .word :: tail) comparison .bool definitions :=
  ⟨by simp [comparison, nested, Expr.wordLt_expansion, Expr.weakenAt],
    Expr.LocalFragment.var.wordLt nestedLocal,
    (HasType.var rfl).wordLt (nestedTyped tail definitions)⟩

theorem arbitrary_definition_typing_reflects_both_original_operands_and_bool_result
    {context : Context} {type : Ty} {definitions : DataEnvironment}
    (typing : HasType context comparison type definitions) :
    type = .bool ∧ HasType context (.var 0) .word definitions ∧
      HasType context nested .word definitions := typing.wordLt_inv_local_right nestedLocal

theorem nonword_operands_and_word_result_are_rejected
    (context : Context) (definitions : DataEnvironment) (word : Word) :
    (¬ HasType context ((Expr.bool true).wordLt (.word word)) .bool definitions) ∧
    (¬ HasType context ((Expr.word word).wordLt (.bool false)) .bool definitions) ∧
    (¬ HasType context comparison .word definitions) := by
  refine ⟨?_, ?_, ?_⟩
  · intro typing
    have invalid := (typing.wordLt_inv_local_right .word).2.1
    cases invalid
  · intro typing
    have invalid := (typing.wordLt_inv_local_right .bool).2.2
    cases invalid
  · intro typing
    have invalid := (typing.wordLt_inv_local_right nestedLocal).1
    cases invalid

theorem original_variable_evaluation_equivalence_fixes_actual_words_and_store
    (left right : Word) (tail : Environment) (store finalStore : Store) (value : Value) :
    Evaluates (environment left right tail) store simple value finalStore ↔
      value = .bool (decide (left < right)) ∧ finalStore = store := by
  rw [show simple = (Expr.var 0).wordLt (.var 1) from rfl,
    wordLt_evaluates_iff_local_right (Expr.LocalFragment.var (index := 1))]
  constructor
  · rintro ⟨actualLeft, actualRight, middleStore, first, second, result⟩
    obtain ⟨leftSame, storeSame⟩ := evaluation_deterministic first (leftEvaluates left right tail store)
    cases leftSame
    subst middleStore
    obtain ⟨rightSame, finalSame⟩ := evaluation_deterministic second (rightEvaluates left right tail store)
    cases rightSame
    exact ⟨result, finalSame⟩
  · rintro ⟨rfl, sameStore⟩
    subst finalStore
    exact ⟨left, right, store, leftEvaluates left right tail store, rightEvaluates left right tail store, rfl⟩

theorem nested_right_forward_and_inversion_recover_original_store_and_words
    (left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment left right tail) store comparison (.bool (decide (left < right))) store ∧
    ∀ value finalStore, Evaluates (environment left right tail) store comparison value finalStore →
      value = .bool (decide (left < right)) ∧ finalStore = store := by
  refine ⟨(leftEvaluates left right tail store).wordLt_local_right
    (nestedEvaluates left right tail store) nestedLocal, ?_⟩
  intro value finalStore evaluation
  obtain ⟨actualLeft, actualRight, middleStore, first, second, result⟩ :=
    evaluation.wordLt_inv_local_right nestedLocal
  obtain ⟨leftSame, storeSame⟩ := evaluation_deterministic first (leftEvaluates left right tail store)
  cases leftSame
  subst middleStore
  obtain ⟨rightSame, finalSame⟩ := evaluation_deterministic second (nestedEvaluates left right tail store)
  cases rightSame
  exact ⟨result, finalSame⟩

theorem equal_strict_and_reversed_words_have_distinct_unsigned_boolean_results
    (left right : Word) (ordered : left < right) (tail : Environment) (store : Store) :
    Evaluates (environment left left tail) store comparison (.bool false) store ∧
    Evaluates (environment left right tail) store comparison (.bool true) store ∧
    Evaluates (environment right left tail) store comparison (.bool false) store := by
  have reversed : ¬right < left := fun opposite => Nat.lt_irrefl left.val (Nat.lt_trans ordered opposite)
  exact ⟨by simpa using (nested_right_forward_and_inversion_recover_original_store_and_words left left tail store).1,
    by simpa [ordered] using (nested_right_forward_and_inversion_recover_original_store_and_words left right tail store).1,
    by simpa [reversed] using (nested_right_forward_and_inversion_recover_original_store_and_words right left tail store).1⟩

theorem missing_original_right_cannot_be_supplied_by_the_generated_left_binding
    (left : Word) (store finalStore : Store) (value : Value) :
    ¬ Evaluates [.word left] store simple value finalStore := by
  intro evaluation
  obtain ⟨_, _, _, _, second, _⟩ := evaluation.wordLt_inv_local_right (Expr.LocalFragment.var (index := 1))
  cases second with
  | var found => cases found

theorem original_variable_paths_compose_to_eleven_steps
    (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 11 ⟨.eval simple (environment left right tail), continuation, store⟩
      ⟨.ret (.bool (decide (left < right))), continuation, store⟩ :=
  Frontend.CostStepComposition.wordLt_of_local_right
    (leftPath left right tail store) (rightPath left right tail store) .var continuation

theorem original_nested_right_paths_compose_to_seventeen_steps
    (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 17 ⟨.eval comparison (environment left right tail), continuation, store⟩
      ⟨.ret (.bool (decide (left < right))), continuation, store⟩ :=
  Frontend.CostStepComposition.wordLt_of_local_right
    (leftPath left right tail store) (nestedPath left right tail store) nestedLocal continuation

theorem exact_fuel_thresholds_distinguish_variable_and_nested_original_right_costs
    (left right : Word) (tail : Environment) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial simple (environment left right tail) store) =
      .done (.bool (decide (left < right))) store ↔ 11 ≤ fuel) ∧
    (runStateful fuel (State.initial comparison (environment left right tail) store) =
      .done (.bool (decide (left < right))) store ↔ 17 ≤ fuel) ∧
    ((∃ checkpoint, runStateful fuel (State.initial comparison (environment left right tail) store) =
      .outOfFuel checkpoint) ↔ fuel < 17) := by
  have simplePath := original_variable_paths_compose_to_eleven_steps left right tail store []
  have complexPath := original_nested_right_paths_compose_to_seventeen_steps left right tail store []
  exact ⟨simplePath.runStateful_done_iff, complexPath.runStateful_done_iff, complexPath.runStateful_outOfFuel_iff⟩

theorem retained_outer_negation_costs_one_more_after_comparison_finishes
    (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 17 ⟨.eval comparison (environment left right tail), .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (.bool (decide (left < right))), .unaryApply .boolNot :: continuation, store⟩ ∧
    Steps 18 ⟨.eval comparison (environment left right tail), .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (.bool (!(decide (left < right)))), continuation, store⟩ := by
  have path := original_nested_right_paths_compose_to_seventeen_steps left right tail store
    (.unaryApply .boolNot :: continuation)
  exact ⟨path, path.trans (.cons (.applyUnary rfl) .refl)⟩

end Tests.CoreLocalRightWordLess
