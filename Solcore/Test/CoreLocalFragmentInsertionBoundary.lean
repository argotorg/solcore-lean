import Solcore.Core.LocalFragment
import Solcore.Core.Machine

/-! Insertion equivalence has a syntactic boundary: creation captures the
environment, every written branch matters, and suspended states remain distinct. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentInsertionBoundary

open Solcore.Core

private def identity : Expr := .lambda .unit .unit (.var 0)
private def skip (unselected : Expr) : Expr := .ifE (.bool true) .unit unselected
private theorem weakenedVar : (Expr.var 0).weakenAt 0 = .var 1 := by simp [Expr.weakenAt]
private theorem weakenedIdentity : identity.weakenAt 0 = identity := by simp [identity, Expr.weakenAt]

theorem unshifted_reference_reads_the_inserted_value_instead_of_the_old_one
    (old inserted : Value) (different : inserted ≠ old) (tail : Environment) (store : Store) :
    Expr.LocalFragment (.var 0) ∧
    Evaluates (old :: tail) store (.var 0) old store ∧
    Evaluates (inserted :: old :: tail) store (.var 0) inserted store ∧
    Evaluates (inserted :: old :: tail) store ((Expr.var 0).weakenAt 0) old store ∧
    runStateful 1 (State.initial (.var 0) (old :: tail) store) ≠
      runStateful 1 (State.initial (.var 0) (inserted :: old :: tail) store) := by
  have original : Evaluates (old :: tail) store (.var 0) old store := .var rfl
  refine ⟨.var, original, .var rfl, original.weakenAt_zero_localFragment .var inserted, ?_⟩
  intro same
  exact different (StatefulRunResult.done.inj same).1.symm

theorem syntactic_membership_does_not_supply_a_missing_variable
    (inserted : Value) (store finalStore : Store) (result : Value) :
    Expr.LocalFragment (.var 0) ∧ Expr.LocalFragment ((Expr.var 0).weakenAt 0) ∧
    ¬Evaluates [] store (.var 0) result finalStore ∧
    ¬Evaluates [inserted] store ((Expr.var 0).weakenAt 0) result finalStore := by
  have absent : ¬Evaluates [] store (.var 0) result finalStore := by
    intro evaluation
    cases evaluation with
    | var lookup => cases lookup
  refine ⟨.var, Expr.LocalFragment.weakenAt .var 0, absent, ?_⟩
  intro evaluation
  exact absent ((Expr.LocalFragment.var.evaluates_weaken_zero_iff [] inserted).mp evaluation)

theorem cell_free_lambda_creation_changes_captures_without_changing_the_store
    (inserted : Value) (environment : Environment) (store : Store) :
    Expr.CellFree identity ∧ ¬Expr.LocalFragment identity ∧
    identity.weakenAt 0 = identity ∧
    Evaluates environment store identity (.closure .unit .unit (.var 0) environment) store ∧
    Evaluates (inserted :: environment) store (identity.weakenAt 0)
      (.closure .unit .unit (.var 0) (inserted :: environment)) store ∧
    ¬Evaluates (inserted :: environment) store (identity.weakenAt 0)
      (.closure .unit .unit (.var 0) environment) store ∧
    runStateful 1 (State.initial identity environment store) ≠
      runStateful 1 (State.initial (identity.weakenAt 0) (inserted :: environment) store) := by
  have different : environment ≠ inserted :: environment := by
    intro same
    have lengths := congrArg List.length same
    simp at lengths
  have captures : (Value.closure .unit .unit (.var 0) environment) ≠
      .closure .unit .unit (.var 0) (inserted :: environment) := by
    intro same
    exact different (Value.closure.inj same).2.2.2
  have actual : Evaluates (inserted :: environment) store (identity.weakenAt 0)
      (.closure .unit .unit (.var 0) (inserted :: environment)) store := by
    rw [weakenedIdentity]
    exact .lambda
  refine ⟨.lambda .var, ?_, weakenedIdentity, .lambda, actual, ?_, ?_⟩
  · intro fragment
    cases fragment
  · intro evaluation
    exact captures (evaluation_deterministic evaluation actual).1
  · rw [weakenedIdentity]
    intro same
    exact captures (StatefulRunResult.done.inj same).1

private theorem skipped_not_local {unselected : Expr} (outside : ¬Expr.LocalFragment unselected) :
    ¬Expr.LocalFragment (skip unselected) := by
  intro fragment
  cases fragment with
  | ifE _ _ branch => exact outside branch

theorem every_written_branch_is_required_even_when_raw_execution_skips_it
    (unselected : Expr) (outside : ¬Expr.LocalFragment unselected) (environment : Environment) (store : Store) :
    ¬Expr.LocalFragment (skip unselected) ∧
    Evaluates environment store (skip unselected) .unit store ∧
    runStateful 4 (State.initial (skip unselected) environment store) = .done .unit store :=
  ⟨skipped_not_local outside, .ifTrue .bool .unit, rfl⟩

theorem skipped_lambda_application_and_cell_access_all_remain_outside_the_fragment
    (environment : Environment) (store : Store) :
    Expr.CellFree (.apply identity .unit) ∧
    ¬Expr.LocalFragment (skip identity) ∧
    ¬Expr.LocalFragment (skip (.apply identity .unit)) ∧
    ¬Expr.LocalFragment (skip (.loadCell (.var 0))) ∧
    runStateful 4 (State.initial (skip identity) environment store) = .done .unit store ∧
    runStateful 4 (State.initial (skip (.apply identity .unit)) environment store) = .done .unit store ∧
    runStateful 4 (State.initial (skip (.loadCell (.var 0))) environment store) = .done .unit store := by
  have lambdaOutside : ¬Expr.LocalFragment identity := by intro fragment; cases fragment
  have callOutside : ¬Expr.LocalFragment (.apply identity .unit) := by intro fragment; cases fragment
  have cellOutside : ¬Expr.LocalFragment (.loadCell (.var 0)) := by intro fragment; cases fragment
  exact ⟨.apply (.lambda .var) .unit, skipped_not_local lambdaOutside,
    skipped_not_local callOutside, skipped_not_local cellOutside, rfl, rfl, rfl⟩

theorem equal_final_values_and_stores_do_not_identify_suspended_states
    (returned inserted : Value) (tail : Environment) (store : Store) :
    runStateful 0 (State.initial (.var 0) (returned :: tail) store) =
      .outOfFuel (State.initial (.var 0) (returned :: tail) store) ∧
    runStateful 0 (State.initial ((Expr.var 0).weakenAt 0) (inserted :: returned :: tail) store) =
      .outOfFuel (State.initial (.var 1) (inserted :: returned :: tail) store) ∧
    runStateful 0 (State.initial (.var 0) (returned :: tail) store) ≠
      runStateful 0 (State.initial ((Expr.var 0).weakenAt 0) (inserted :: returned :: tail) store) ∧
    runStateful 1 (State.initial (.var 0) (returned :: tail) store) = .done returned store ∧
    runStateful 1 (State.initial ((Expr.var 0).weakenAt 0) (inserted :: returned :: tail) store) =
      .done returned store := by
  rw [weakenedVar]
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  intro same
  cases same

end Tests.CoreLocalFragmentInsertionBoundary
