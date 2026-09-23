import Solcore.Core.LocalFragment
import Solcore.Core.Derived
import Solcore.Core.FuelResumptionProperties

/-! Exact final costs survive insertion; genuine let checkpoints do not become
equal. Every transported outer continuation remains pending and unchanged. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentExactInsertionBoundary

open Solcore.Core

private def less : Expr := .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))
private def environment (left right : Word) (tail : Environment) : Environment := .word right :: .word left :: tail
private def result (left right : Word) : Value := .bool (decide (left < right))
private theorem lessFragment : less.LocalFragment := .letE .var (.letE .var (.binary .var .var))
private theorem shiftedLess : less.weakenAt 0 =
    .letE (.var 2) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1))) := by
  simp [less, Expr.weakenAt]
private def originalCheckpoint (left right : Word) (tail : Environment) (store : Store) : State :=
  ⟨.ret (.word left), [.letBody (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))
    (environment left right tail)], store⟩
private def shiftedCheckpoint (left right : Word) (tail : Environment) (inserted : Value) (store : Store) : State :=
  ⟨.ret (.word left), [.letBody (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
    (inserted :: environment left right tail)], store⟩
private theorem originalPath (left right : Word) (tail : Environment) (store : Store) :
    Steps 11 (State.initial less (environment left right tail) store) (State.final (result left right) store) :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet
    (.cons .enterLet (.cons (.var rfl) (.cons .bindLet
      (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight
        (.cons (.var rfl) (.cons (.applyBinary rfl) .refl))))))))))

theorem ordered_word_less_expansion_retains_eleven_steps_and_exact_closed_path_equivalence
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) (cost : Nat) :
    less = (Expr.var 1).wordLt (.var 0) ∧ less.LocalFragment ∧
    Steps 11 (State.initial less (environment left right tail) store) (State.final (result left right) store) ∧
    Steps 11 (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store)
      (State.final (result left right) store) ∧
    (Steps cost (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store)
        (State.final (result left right) store) ↔
      Steps cost (State.initial less (environment left right tail) store) (State.final (result left right) store)) := by
  refine ⟨?_, lessFragment, originalPath left right tail store,
    (originalPath left right tail store).weakenAt_zero_localFragment lessFragment inserted [],
    lessFragment.steps_insert_iff [] (environment left right tail) inserted⟩
  simp [less, Expr.wordLt_expansion, Expr.weakenAt]

theorem completion_and_exhaustion_thresholds_match_without_equating_full_results
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial less (environment left right tail) store) =
      .done (result left right) store ↔ 11 ≤ fuel) ∧
    (runStateful fuel (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) =
      .done (result left right) store ↔ 11 ≤ fuel) ∧
    ((∃ state, runStateful fuel (State.initial less (environment left right tail) store) = .outOfFuel state) ↔
      fuel < 11) ∧
    ((∃ state, runStateful fuel (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) =
      .outOfFuel state) ↔ fuel < 11) := by
  have original := originalPath left right tail store
  have shifted := original.weakenAt_zero_localFragment lessFragment inserted []
  exact ⟨original.runStateful_done_iff, shifted.runStateful_done_iff,
    original.runStateful_outOfFuel_iff, shifted.runStateful_outOfFuel_iff⟩

theorem distinct_genuine_let_checkpoints_resume_independently_with_nine_remaining_steps
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) (additional : Nat) :
    runStateful 2 (State.initial less (environment left right tail) store) =
      .outOfFuel (originalCheckpoint left right tail store) ∧
    runStateful 2 (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) =
      .outOfFuel (shiftedCheckpoint left right tail inserted store) ∧
    originalCheckpoint left right tail store ≠ shiftedCheckpoint left right tail inserted store ∧
    Steps 9 (originalCheckpoint left right tail store) (State.final (result left right) store) ∧
    Steps 9 (shiftedCheckpoint left right tail inserted store) (State.final (result left right) store) ∧
    runStateful additional (originalCheckpoint left right tail store) =
      runStateful (2 + additional) (State.initial less (environment left right tail) store) ∧
    runStateful additional (shiftedCheckpoint left right tail inserted store) =
      runStateful (2 + additional) (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) ∧
    (runStateful additional (shiftedCheckpoint left right tail inserted store) =
      .done (result left right) store ↔ 9 ≤ additional) := by
  have original := originalPath left right tail store
  have shifted := original.weakenAt_zero_localFragment lessFragment inserted []
  have first : runStateful 2 (State.initial less (environment left right tail) store) =
      .outOfFuel (originalCheckpoint left right tail store) := rfl
  have second : runStateful 2 (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) =
      .outOfFuel (shiftedCheckpoint left right tail inserted store) := by rw [shiftedLess]; rfl
  refine ⟨first, second, ?_, (original.residual_of_outOfFuel first).2, (shifted.residual_of_outOfFuel second).2,
    runStateful_resume first additional, runStateful_resume second additional, shifted.resumed_done_iff second⟩
  intro same
  cases same

theorem arbitrary_nonempty_continuations_are_retained_not_rewritten_or_executed
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) (outer : List Frame) :
    Steps 11 ⟨.eval less (environment left right tail), .unaryApply .boolNot :: outer, store⟩
      ⟨.ret (result left right), .unaryApply .boolNot :: outer, store⟩ ∧
    Steps 11 ⟨.eval (less.weakenAt 0) (inserted :: environment left right tail), .unaryApply .boolNot :: outer, store⟩
      ⟨.ret (result left right), .unaryApply .boolNot :: outer, store⟩ ∧
    Steps 12 ⟨.eval (less.weakenAt 0) (inserted :: environment left right tail), .unaryApply .boolNot :: outer, store⟩
      ⟨.ret (.bool (!(decide (left < right)))), outer, store⟩ := by
  have shiftedClosed := (originalPath left right tail store).weakenAt_zero_localFragment lessFragment inserted []
  have original := shiftedClosed.reflect_weakenAt_zero_localFragment lessFragment (.unaryApply .boolNot :: outer)
  have shifted := lessFragment.steps_insert [] (environment left right tail) inserted
    (originalPath left right tail store) (.unaryApply .boolNot :: outer)
  exact ⟨original, shifted, shifted.trans (.cons (.applyUnary rfl) .refl)⟩

theorem eleven_fuel_still_exhausts_when_the_retained_outer_negation_has_not_run
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) :
    runStateful 11 ⟨.eval (less.weakenAt 0) (inserted :: environment left right tail), [.unaryApply .boolNot], store⟩ =
      .outOfFuel ⟨.ret (result left right), [.unaryApply .boolNot], store⟩ ∧
    runStateful 12 ⟨.eval (less.weakenAt 0) (inserted :: environment left right tail), [.unaryApply .boolNot], store⟩ =
      .done (.bool (!(decide (left < right)))) store := by
  have paths := arbitrary_nonempty_continuations_are_retained_not_rewritten_or_executed left right tail inserted store []
  exact ⟨runStateful_outOfFuel_complete paths.2.1 rfl, paths.2.2.runStateful_done_iff.mpr (by decide)⟩

private def badBranch : Expr := .unary .wordNot (.bool false)
private def skipped : Expr := .ifE (.bool true) .unit badBranch
private theorem skippedFragment : skipped.LocalFragment := .ifE .bool .unit (.unary .bool)
private theorem skippedPath (environment : Environment) (store : Store) :
    Steps 4 (State.initial skipped environment store) (State.final .unit store) :=
  .cons .enterIf (.cons .bool (.cons .chooseTrue (.cons .unit .refl)))

theorem unselected_structural_but_ill_typed_children_do_not_contribute_path_cost
    (environment : Environment) (inserted : Value) (store : Store) (context : Context) (definitions : DataEnvironment) :
    skipped.LocalFragment ∧ (∀ type, ¬HasType context skipped type definitions) ∧
    Evaluates environment store skipped .unit store ∧
    (∀ continuation,
      Steps 4 ⟨.eval skipped environment, continuation, store⟩ ⟨.ret .unit, continuation, store⟩ ∧
      Steps 4 ⟨.eval (skipped.weakenAt 0) (inserted :: environment), continuation, store⟩
        ⟨.ret .unit, continuation, store⟩) := by
  have evaluation : Evaluates environment store skipped .unit store := .ifTrue .bool .unit
  obtain ⟨cost, paired⟩ := skippedFragment.insertion_paths [] environment inserted evaluation
  have sameCost := ((skippedPath environment store).final_unique (paired []).1).1
  refine ⟨skippedFragment, ?_, evaluation, ?_⟩
  · intro type typing
    cases typing with
    | ifE _ _ rejected =>
        cases rejected with
        | unary child => cases child
  · exact sameCost ▸ paired

end Tests.CoreLocalFragmentExactInsertionBoundary
