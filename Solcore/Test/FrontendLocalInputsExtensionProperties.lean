import Solcore.Frontend.LocalInputsExtensionProperties

/-! Adding an unused spelling shifts positional Core references without
changing existing identity-based meanings. Fresh IDs alone do not suffice. -/

set_option autoImplicit false

namespace Tests.FrontendLocalInputsExtension

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Extension", by decide⟩], by decide⟩⟩, 0⟩
private def localId (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "extension.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional condition span left span right⟩
private def inputs (choice : Bool) : LocalInputs :=
  (((LocalInputs.empty.bindFresh owner "w" .word (.word Core.Word.zero) .word).bindFresh
    owner "e" .bool (.bool true) .bool).bindFresh owner "t" .bool (.bool false) .bool).bindFresh
      owner "c" .bool (.bool choice) .bool
private def extended (choice : Bool) : LocalInputs :=
  (inputs choice).bindFresh owner "extra" .unit .unit .unit
private def names : LocalNameTable :=
  [("c", localId 3), ("t", localId 2), ("e", localId 1), ("w", localId 0)]
private def context : Resolved.Context :=
  [(localId 3, .bool), (localId 2, .bool), (localId 1, .bool), (localId 0, .word)]
private def source : Syntax.Expr := branch (ref "c") (ref "t") (ref "e")
private def resolved : Resolved.Expr :=
  .ifE (.var (localId 3)) (.var (localId 2)) (.var (localId 1))
private def core : Core.Expr := .ifE (.var 0) (.var 1) (.var 2)
private def shifted : Core.Expr := .ifE (.var 1) (.var 2) (.var 3)
private theorem avoids_source : AvoidsLocalName "extra" source :=
  .conditional (.identifier (by decide)) (.identifier (by decide)) (.identifier (by decide))
private theorem resolution (choice : Bool) : ResolvesLocalExpression (inputs choice).names source resolved := by
  change ResolvesLocalExpression names source resolved
  exact .conditional (.identifier .head) (.identifier (.tail (by decide) .head))
    (.identifier (.tail (by decide) (.tail (by decide) .head)))
private theorem checked (choice : Bool) : (inputs choice).check? source = some (core, .bool) := by
  apply elaborateLocalExpression?_complete (resolution choice)
  · change Resolved.Lowers (Resolved.LocalScope.ids context) resolved core
    exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))
  · change Resolved.HasType context resolved .bool
    exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))

private theorem checked_extended (choice : Bool) :
    (extended choice).check? source = some (shifted, .bool) := by
  simpa [extended, core, shifted, Core.Expr.weakenAt] using
    avoids_source.check_bindFresh_complete (inputs choice) owner .unit .unit .unit (checked choice)

theorem unused_name_keeps_identities_and_shifts_core (choice : Bool) (store : Core.Store) :
    resolveLocalExpression? (inputs choice).names source = some resolved ∧
    resolveLocalExpression? (extended choice).names source = some resolved ∧
    (inputs choice).check? source = some (core, .bool) ∧
    (extended choice).check? source = some (shifted, .bool) ∧
    (inputs choice).run? 4 source store = some (.bool, .done (.bool (!choice)) store) ∧
    (extended choice).run? 4 source store = some (.bool, .done (.bool (!choice)) store) := by
  refine ⟨(resolution choice).complete,
    (avoids_source.resolves_cons_iff.mpr (resolution choice)).complete,
    checked choice, checked_extended choice, ?_, ?_⟩
  · rw [LocalInputs.run?, checked]; cases choice <;> rfl
  · rw [LocalInputs.run?, checked_extended]; cases choice <;> rfl

theorem unused_name_preserves_type_and_both_evaluation_stores (choice : Bool)
    (type : Core.Ty) (value : Core.Value) (initialStore finalStore : Core.Store) :
    (LocalExpressionHasType (extended choice).names (extended choice).context source type ↔
      LocalExpressionHasType (inputs choice).names (inputs choice).context source type) ∧
    (LocalExpressionEvaluates (extended choice).names (extended choice).environment initialStore source value finalStore ↔
      LocalExpressionEvaluates (inputs choice).names (inputs choice).environment initialStore source value finalStore) ∧
    ((∃ fuel, (extended choice).run? fuel source initialStore = some (type, .done value finalStore)) ↔
      ∃ fuel, (inputs choice).run? fuel source initialStore = some (type, .done value finalStore)) :=
  ⟨avoids_source.bindFresh_hasType_iff (inputs choice) owner .unit .unit .unit,
    avoids_source.bindFresh_evaluates_iff (inputs choice) owner .unit .unit .unit,
    avoids_source.bindFresh_run_done_iff (inputs choice) owner .unit .unit .unit⟩

private def illTyped : Syntax.Expr := branch (ref "w") (ref "t") (ref "e")
private theorem avoids_illTyped : AvoidsLocalName "extra" illTyped :=
  .conditional (.identifier (by decide)) (.identifier (by decide)) (.identifier (by decide))

theorem supported_illtyped_checks_remain_absent :
    AvoidsLocalName "extra" illTyped ∧
    resolveLocalExpression? (inputs true).names illTyped =
      some (.ifE (.var (localId 0)) (.var (localId 2)) (.var (localId 1))) ∧
    (inputs true).check? illTyped = none ∧
      (extended true).check? illTyped = none := by
  have rejected : (inputs true).check? illTyped = none := by
    change elaborateLocalExpression? names context illTyped = none
    simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
      illTyped, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids, Resolved.LocalScope.values,
      Resolved.LocalScope.index?, localId]
    intro type inferred
    cases Core.infer_sound inferred with
    | ifE condition _ _ => cases condition with | var found => cases found
  refine ⟨avoids_illTyped, ?_, rejected, ?_⟩
  · apply ResolvesLocalExpression.complete
    exact .conditional
      (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.identifier (.tail (by decide) .head))
      (.identifier (.tail (by decide) (.tail (by decide) .head)))
  · change ((inputs true).bindFresh owner "extra" .unit .unit .unit).check? illTyped = none
    rw [avoids_illTyped.check_bindFresh_eq, rejected]
    rfl

private def unselectedMissing : Syntax.Expr := branch (ref "c") (ref "t") (ref "missing")
private theorem avoids_missing : AvoidsLocalName "extra" unselectedMissing :=
  .conditional (.identifier (by decide)) (.identifier (by decide)) (.identifier (by decide))

theorem unselected_missing_name_stays_evaluable_but_unchecked (store : Core.Store) :
    LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      unselectedMissing (.bool false) store ∧
    LocalExpressionEvaluates (extended true).names (extended true).environment store
      unselectedMissing (.bool false) store ∧
    (inputs true).check? unselectedMissing = none ∧ (extended true).check? unselectedMissing = none := by
  have evaluation : LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      unselectedMissing (.bool false) store :=
    .ifTrue (.identifier .head .head) (.identifier (.tail (by decide) .head) (.tail (by decide) .head))
  have rejected : (inputs true).check? unselectedMissing = none := by
    change elaborateLocalExpression? names context unselectedMissing = none
    simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?,
      names, unselectedMissing, branch, ref]
  refine ⟨evaluation, (avoids_missing.bindFresh_evaluates_iff (inputs true) owner .unit .unit .unit).mpr evaluation,
    rejected, ?_⟩
  change ((inputs true).bindFresh owner "extra" .unit .unit .unit).check? unselectedMissing = none
  rw [avoids_missing.check_bindFresh_eq, rejected]
  rfl

private def changed : LocalInputs := (inputs true).bindFresh owner "c" .bool (.bool false) .bool
private def changedCore : Core.Expr := .ifE (.var 0) (.var 2) (.var 3)
private theorem checked_changed : changed.check? source = some (changedCore, .bool) := by
  apply elaborateLocalExpression?_complete
    (resolved := .ifE (.var (localId 4)) (.var (localId 2)) (.var (localId 1)))
  · exact .conditional (.identifier .head) (.identifier (.tail (by decide) (.tail (by decide) .head)))
      (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
  · exact .ifE (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
  · exact .ifE (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))

theorem a_used_condition_name_changes_results_despite_fresh_identity (store : Core.Store) :
    Resolved.freshLocalId owner (inputs true).ids ∉ (inputs true).ids ∧
    (¬ AvoidsLocalName "c" source) ∧ changed.check? source = some (changedCore, .bool) ∧
    (inputs true).run? 4 source store = some (.bool, .done (.bool false) store) ∧
    changed.run? 4 source store = some (.bool, .done (.bool true) store) := by
  refine ⟨(inputs true).bindFresh_id_fresh owner, ?_, checked_changed, ?_, ?_⟩
  · intro avoids
    cases avoids with
    | conditional condition _ _ => cases condition with | identifier different => exact different rfl
  · rw [LocalInputs.run?, checked]; rfl
  · rw [LocalInputs.run?, checked_changed]; rfl

end Tests.FrontendLocalInputsExtension
