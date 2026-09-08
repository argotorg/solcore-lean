import Solcore.Core.ExactFuelProperties

/-! Exact thresholds require a terminal path. Final-state recognition is free;
a proper nonterminal prefix does not supply a completion bound. -/

set_option autoImplicit false

namespace Tests.CoreExactFuel

open Solcore.Core

theorem already_final_needs_zero_transitions (value : Value) (store : Store) (fuel : Nat) :
    runStateful fuel (State.final value store) = .done value store ∧
    (¬ ∃ suspended, runStateful fuel (State.final value store) = .outOfFuel suspended) ∧
    ∀ steps otherValue otherStore, Steps steps (State.final value store) (State.final otherValue otherStore) →
      steps = 0 ∧ otherValue = value ∧ otherStore = store := by
  have path : Steps 0 (State.final value store) (State.final value store) := .refl
  refine ⟨path.runStateful_done_iff.mpr (Nat.zero_le _), ?_, ?_⟩
  · rw [path.runStateful_outOfFuel_iff]
    omega
  · intro steps otherValue otherStore otherPath
    exact otherPath.final_unique path

theorem a_literal_terminal_path_has_exact_one_transition_boundary
    (word : Word) (environment : Environment) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial (.word word) environment store) = .done (.word word) store ↔ 1 ≤ fuel) ∧
    ((∃ suspended, runStateful fuel (State.initial (.word word) environment store) = .outOfFuel suspended) ↔ fuel < 1) ∧
    runStateful 0 (State.initial (.word word) environment store) =
      .outOfFuel (State.initial (.word word) environment store) := by
  have path : Steps 1 (State.initial (.word word) environment store) (State.final (.word word) store) :=
    .cons .word .refl
  exact ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff, rfl⟩

theorem a_nonterminal_prefix_is_not_a_completion_bound (environment : Environment) (store : Store) :
    Steps 1 (State.initial (.unary .boolNot (.bool false)) environment store)
      ⟨.eval (.bool false) environment, [.unaryApply .boolNot], store⟩ ∧
    runStateful 1 (State.initial (.unary .boolNot (.bool false)) environment store) =
      .outOfFuel ⟨.eval (.bool false) environment, [.unaryApply .boolNot], store⟩ ∧
    Steps 3 (State.initial (.unary .boolNot (.bool false)) environment store) (State.final (.bool true) store) ∧
    runStateful 3 (State.initial (.unary .boolNot (.bool false)) environment store) = .done (.bool true) store ∧
    (1 : Nat) < 3 := by
  have path : Steps 3 (State.initial (.unary .boolNot (.bool false)) environment store) (State.final (.bool true) store) :=
    .cons .enterUnary (.cons .bool (.cons (.applyUnary rfl) .refl))
  exact ⟨.cons .enterUnary .refl, rfl, path, path.runStateful_done_iff.mpr (Nat.le_refl _), by decide⟩

theorem returning_with_a_pending_frame_is_not_final (word : Word) (store : Store) :
    Steps 0 ⟨.ret (.word word), [.unaryApply .wordNot], store⟩
      ⟨.ret (.word word), [.unaryApply .wordNot], store⟩ ∧
    runStateful 0 ⟨.ret (.word word), [.unaryApply .wordNot], store⟩ =
      .outOfFuel ⟨.ret (.word word), [.unaryApply .wordNot], store⟩ ∧
    runStateful 1 ⟨.ret (.word word), [.unaryApply .wordNot], store⟩ =
      .done (.word word.bitNot) store :=
  ⟨.refl, rfl, rfl⟩

end Tests.CoreExactFuel
