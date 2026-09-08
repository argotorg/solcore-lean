import Solcore.Core.LocalRightWordLessTypingProperties
import Solcore.Core.LocalRightWordLessEvaluationProperties
import Solcore.Frontend.WordLessLocalRightCostProperties
import Solcore.Core.FuelResumptionProperties

/-! The left operand may allocate before a local right reference is evaluated.
An unrestricted right operand can instead expose changed closure captures in
the store; that counterexample deliberately uses raw, untyped cell allocation. -/

set_option autoImplicit false

namespace Tests.CoreLocalRightWordLessBoundary

open Solcore Solcore.Core

private def allocating (allocated left : Word) : Expr := .letE (.newCell .word (.word allocated)) (.word left)
private def comparisonBody : Expr := .letE (.var 1) (.binary .wordGt (.var 0) (.var 1))
private def whole (allocated left : Word) : Expr := (allocating allocated left).wordLt (.var 0)
private def environment (right : Word) (tail : Environment) : Environment := .word right :: tail
private def grown (store : Store) (allocated : Word) : Store := store ++ [.word allocated]
private def result (left right : Word) : Value := .bool (decide (left < right))
private theorem wholeShape (allocated left : Word) :
    whole allocated left = .letE (allocating allocated left) comparisonBody := by
  simp [whole, comparisonBody, Expr.wordLt_expansion, Expr.weakenAt]
private theorem allocatingEvaluation (allocated left : Word) (environment : Environment) (store : Store) :
    Evaluates environment store (allocating allocated left) (.word left) (grown store allocated) :=
  .letE (.newCell .word) .word
private theorem allocatingPath (allocated left : Word) (environment : Environment) (store : Store)
    (continuation : List Frame) :
    Steps 6 ⟨.eval (allocating allocated left) environment, continuation, store⟩
      ⟨.ret (.word left), continuation, grown store allocated⟩ :=
  .cons .enterLet (.cons .enterNewCell (.cons .word (.cons .applyNewCell (.cons .bindLet (.cons .word .refl)))))

theorem left_allocation_is_nonlocal_but_ordinary_word_typing_is_recovered
    (allocated left : Word) (tail : Context) (definitions : DataEnvironment) :
    ¬Expr.LocalFragment (allocating allocated left) ∧
    HasType (.word :: tail) (whole allocated left) .bool definitions ∧
    HasType (.word :: tail) (allocating allocated left) .word definitions ∧
    HasType (.word :: tail) (.var 0) .word definitions := by
  have leftTyped : HasType (.word :: tail) (allocating allocated left) .word definitions :=
    .letE (.newCell .word .word) .word
  have typed := leftTyped.wordLt (show HasType (.word :: tail) (.var 0) .word definitions from .var rfl)
  have originalOperands := typed.wordLt_inv_local_right .var
  refine ⟨?_, typed, originalOperands.2.1, originalOperands.2.2⟩
  intro fragment
  cases fragment with
  | letE allocation _ => cases allocation

theorem raw_forward_and_inverse_preserve_the_actual_allocated_intermediate_store
    (allocated left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment right tail) store (allocating allocated left) (.word left) (grown store allocated) ∧
    Evaluates (environment right tail) (grown store allocated) (.var 0) (.word right) (grown store allocated) ∧
    Evaluates (environment right tail) store (whole allocated left) (result left right) (grown store allocated) ∧
    (∀ value finalStore, Evaluates (environment right tail) store (whole allocated left) value finalStore →
      value = result left right ∧ finalStore = grown store allocated) := by
  have first := allocatingEvaluation allocated left (environment right tail) store
  have second : Evaluates (environment right tail) (grown store allocated) (.var 0) (.word right)
      (grown store allocated) := .var rfl
  refine ⟨first, second, first.wordLt_local_right second .var, ?_⟩
  intro value finalStore evaluation
  obtain ⟨actualLeft, actualRight, middle, leftEvaluation, rightEvaluation, valueEq⟩ :=
    evaluation.wordLt_inv_local_right .var
  have firstEq := evaluation_deterministic leftEvaluation first
  have leftEq := Value.word.inj firstEq.1
  have middleEq := firstEq.2
  subst actualLeft middle
  have secondEq := evaluation_deterministic rightEvaluation second
  have rightEq := Value.word.inj secondEq.1
  subst actualRight
  exact ⟨valueEq, secondEq.2⟩

theorem allocating_left_and_original_right_paths_compose_to_exactly_sixteen
    (allocated left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 16 ⟨.eval (whole allocated left) (environment right tail), continuation, store⟩
      ⟨.ret (result left right), continuation, grown store allocated⟩ :=
  Frontend.CostStepComposition.wordLt_of_local_right
    (allocatingPath allocated left (environment right tail) store)
    (fun _ => .cons (.var rfl) .refl) .var continuation

private def beforeAllocation (allocated left right : Word) (tail : Environment) (store : Store) : State :=
  ⟨.ret (.word allocated), [.newCellApply .word, .letBody (.word left) (environment right tail),
    .letBody comparisonBody (environment right tail)], store⟩
private def afterAllocation (allocated left right : Word) (tail : Environment) (store : Store) : State :=
  ⟨.ret (.cellRef .word store.length), [.letBody (.word left) (environment right tail),
    .letBody comparisonBody (environment right tail)], grown store allocated⟩
private def beforeRight (allocated left right : Word) (tail : Environment) (store : Store) : State :=
  ⟨.eval (.var 1) (.word left :: environment right tail),
    [.letBody (.binary .wordGt (.var 0) (.var 1)) (.word left :: environment right tail)], grown store allocated⟩

theorem genuine_checkpoints_show_allocation_finishes_before_the_right_reference_starts
    (allocated left right : Word) (tail : Environment) (store : Store) :
    runStateful 4 (State.initial (whole allocated left) (environment right tail) store) =
      .outOfFuel (beforeAllocation allocated left right tail store) ∧
    runStateful 5 (State.initial (whole allocated left) (environment right tail) store) =
      .outOfFuel (afterAllocation allocated left right tail store) ∧
    runStateful 9 (State.initial (whole allocated left) (environment right tail) store) =
      .outOfFuel (beforeRight allocated left right tail store) ∧
    store ≠ grown store allocated := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [wholeShape]; rfl
  · rw [wholeShape]; rfl
  · rw [wholeShape]; rfl
  · intro same
    have lengths := congrArg List.length same
    simp [grown] at lengths

theorem exact_fuel_and_resumption_keep_the_allocated_store_and_pending_right_environment
    (allocated left right : Word) (tail : Environment) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial (whole allocated left) (environment right tail) store) =
      .done (result left right) (grown store allocated) ↔ 16 ≤ fuel) ∧
    ((∃ state, runStateful fuel (State.initial (whole allocated left) (environment right tail) store) =
      .outOfFuel state) ↔ fuel < 16) ∧
    Steps 7 (beforeRight allocated left right tail store) (State.final (result left right) (grown store allocated)) ∧
    runStateful fuel (beforeRight allocated left right tail store) =
      runStateful (9 + fuel) (State.initial (whole allocated left) (environment right tail) store) ∧
    (runStateful fuel (beforeRight allocated left right tail store) =
      .done (result left right) (grown store allocated) ↔ 7 ≤ fuel) := by
  have path := allocating_left_and_original_right_paths_compose_to_exactly_sixteen allocated left right tail store []
  have checkpoint :=
    (genuine_checkpoints_show_allocation_finishes_before_the_right_reference_starts allocated left right tail store).2.2.1
  exact ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff, (path.residual_of_outOfFuel checkpoint).2,
    runStateful_resume checkpoint fuel, path.resumed_done_iff checkpoint⟩

/-- This is deliberately raw, untyped allocation: function values are not
legal typed cell payloads. It witnesses the need for a local right operand in
the new untyped bridge, not an admitted typed frontend program. -/
private def capturingRight (right : Word) : Expr :=
  .letE (.newCell (.function .unit .unit) (.lambda .unit .unit (.var 0))) (.word right)
private def originalCapture : Value := .closure .unit .unit (.var 0) []
private def shiftedCapture (left : Word) : Value := .closure .unit .unit (.var 0) [.word left]

theorem a_word_returning_right_operand_can_store_distinct_captures_after_insertion
    (left right : Word) (store : Store) :
    ¬Expr.LocalFragment (capturingRight right) ∧
    (∀ type, ¬HasType [] (capturingRight right) type) ∧
    Evaluates [] store (capturingRight right) (.word right) (store ++ [originalCapture]) ∧
    Evaluates [.word left] store ((capturingRight right).weakenAt 0) (.word right)
      (store ++ [shiftedCapture left]) ∧
    store ++ [originalCapture] ≠ store ++ [shiftedCapture left] := by
  refine ⟨?_, ?_, .letE (.newCell .lambda) .word, ?_, ?_⟩
  · intro fragment
    cases fragment with
    | letE allocation _ => cases allocation
  · intro type typing
    cases typing with
    | letE allocation _ =>
        cases allocation with
        | newCell _ payload => cases payload
  · simp only [capturingRight, Expr.weakenAt]
    exact .letE (.newCell .lambda) .word
  · intro same
    have captured := (List.cons.inj (List.append_cancel_left same)).1
    cases captured

theorem dropping_the_right_fragment_premise_would_make_the_exact_store_bridge_false
    (left right : Word) (store : Store) :
    Evaluates [] store (.word left) (.word left) store ∧
    Evaluates [] store (capturingRight right) (.word right) (store ++ [originalCapture]) ∧
    Evaluates [] store ((Expr.word left).wordLt (capturingRight right)) (result left right)
      (store ++ [shiftedCapture left]) ∧
    ¬Evaluates [] store ((Expr.word left).wordLt (capturingRight right)) (result left right)
      (store ++ [originalCapture]) := by
  obtain ⟨_, _, originalRight, shiftedRight, different⟩ :=
    a_word_returning_right_operand_can_store_distinct_captures_after_insertion left right store
  have actual : Evaluates [] store ((Expr.word left).wordLt (capturingRight right)) (result left right)
      (store ++ [shiftedCapture left]) := by
    rw [Expr.wordLt_expansion]
    exact .letE .word (.letE shiftedRight (.binary (.var rfl) (.var rfl) rfl))
  refine ⟨.word, originalRight, actual, ?_⟩
  intro impossible
  exact different (evaluation_deterministic impossible actual).2

end Tests.CoreLocalRightWordLessBoundary
