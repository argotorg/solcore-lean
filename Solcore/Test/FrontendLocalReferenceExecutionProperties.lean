import Solcore.Frontend.LocalReference

/-! Checked canonical references preserve values only when context and runtime
identity order agree. Equal positional types alone do not establish that alignment. -/

set_option autoImplicit false

namespace Tests.FrontendLocalReferenceExecution

open Solcore Solcore.Frontend

private def modulePath : Workspace.ModulePath := ⟨[⟨"ReferenceExec", by decide⟩], by decide⟩
private def idA : Resolved.LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, 0⟩
private def idB : Resolved.LocalId := { idA with binderIndex := 1 }
private def span : Syntax.SourceSpan := ⟨⟨.main, "refs.sol"⟩, 0, 4⟩
private def source : Syntax.Expr :=
  ⟨span, .group ⟨span, .identifier ⟨span, "flag"⟩⟩⟩
private def table : LocalNameTable := [("flag", idA)]
private def context : Resolved.Context := [(idA, .bool), (idB, .bool)]
private def aligned : Resolved.Environment := [(idA, .bool false), (idB, .bool true)]
private def reversed : Resolved.Environment := [(idB, .bool true), (idA, .bool false)]

private theorem reference : ResolvesLocalReference table source idA :=
  .group (.identifier .head)

private theorem aligned_typed : Core.EnvironmentHasTypes
    (Resolved.LocalScope.values aligned) (Resolved.LocalScope.values context) :=
  .cons .bool (.cons .bool .nil)

private theorem aligned_evaluates : LocalReferenceEvaluates table aligned source (.bool false) :=
  .reference reference .head

theorem checked_reference_selects_first_position :
    elaborateLocalReference? table context source = some (.var 0, .bool) :=
  elaborateLocalReference?_complete reference .head .head

theorem aligned_typed_execution (store : Core.Store) :
    LocalReferenceEvaluates table aligned source (.bool false) ∧
    Core.ValueHasType (.bool false) .bool ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 0) (Resolved.LocalScope.values aligned) store) =
        .done (.bool false) store := by
  obtain ⟨value, evaluation, valueTyped, enough⟩ :=
    elaborateLocalReference?_typed_execution checked_reference_selects_first_position
      (environment := aligned) rfl aligned_typed store
  cases evaluation.deterministic aligned_evaluates
  exact ⟨aligned_evaluates, valueTyped, enough⟩

theorem aligned_exact_machine_boundary (store : Core.Store) :
    Core.runStateful 0
      (Core.State.initial (.var 0) (Resolved.LocalScope.values aligned) store) =
        .outOfFuel (Core.State.initial (.var 0) (Resolved.LocalScope.values aligned) store) ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 0) (Resolved.LocalScope.values aligned) store) =
        .done (.bool false) store :=
  elaborateLocalReference?_exact_run checked_reference_selects_first_position
    rfl aligned_evaluates store

theorem aligned_checked_evaluation_iff (initialStore finalStore : Core.Store) (value : Core.Value) :
    Core.Evaluates (Resolved.LocalScope.values aligned) initialStore (.var 0) value finalStore ↔
      LocalReferenceEvaluates table aligned source value ∧ finalStore = initialStore :=
  elaborateLocalReference?_evaluates_iff checked_reference_selects_first_position rfl

/-- Reordering preserves all Boolean types and each ID's value, but breaks the
identity alignment required by checked execution. The reference still denotes A. -/
theorem reversed_environment_is_typed_but_misaligned :
    Core.EnvironmentHasTypes (Resolved.LocalScope.values reversed)
      (Resolved.LocalScope.values context) ∧
    Resolved.LocalScope.ids reversed ≠ Resolved.LocalScope.ids context ∧
    LocalReferenceEvaluates table reversed source (.bool false) :=
  ⟨.cons .bool (.cons .bool .nil), by decide,
    .reference reference (.tail (by decide) .head)⟩

/-- Without identity alignment, the checked Core position reads B's true while
the same canonical reference independently reads A's false. -/
theorem reversed_core_reads_the_wrong_reference_value (store : Core.Store) :
    Core.Evaluates (Resolved.LocalScope.values reversed) store (.var 0) (.bool true) store ∧
    (∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 0) (Resolved.LocalScope.values reversed) store) =
        .done (.bool true) store) ∧
    ¬ LocalReferenceEvaluates table reversed source (.bool true) := by
  refine ⟨.var rfl, ?_, ?_⟩
  · intro fuel
    simp [Core.runStateful, Core.State.initial, Core.advance, Resolved.LocalScope.values, reversed]
  · intro evaluation
    have impossible := evaluation.deterministic reversed_environment_is_typed_but_misaligned.2.2
    cases impossible

private def duplicateContext : Resolved.Context := [(idA, .bool), (idA, .bool)]
private def duplicateEnvironment : Resolved.Environment := [(idA, .bool false), (idA, .bool true)]

theorem duplicate_ids_keep_first_typed_value (store : Core.Store) :
    elaborateLocalReference? table duplicateContext source = some (.var 0, .bool) ∧
    LocalReferenceEvaluates table duplicateEnvironment source (.bool false) ∧
    Core.ValueHasType (.bool false) .bool ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 0) (Resolved.LocalScope.values duplicateEnvironment) store) =
        .done (.bool false) store := by
  have accepted : elaborateLocalReference? table duplicateContext source = some (.var 0, .bool) :=
    elaborateLocalReference?_complete reference .head .head
  have environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values duplicateEnvironment) (Resolved.LocalScope.values duplicateContext) :=
    .cons .bool (.cons .bool .nil)
  obtain ⟨value, evaluation, valueTyped, enough⟩ :=
    elaborateLocalReference?_typed_execution accepted
      (environment := duplicateEnvironment) rfl environmentTyped store
  have first : LocalReferenceEvaluates table duplicateEnvironment source (.bool false) :=
    .reference reference .head
  cases evaluation.deterministic first
  exact ⟨accepted, first, valueTyped, enough⟩

end Tests.FrontendLocalReferenceExecution
