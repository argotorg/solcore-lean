import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.LocalInputsExecutionProperties
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.LocalExpressionEvaluationProperties

/-! Shared typed inputs keep identity order synchronized. Fresh identity
allocation does not prevent deliberate first-match spelling shadowing. -/

set_option autoImplicit false

namespace Tests.FrontendLocalInputs

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Inputs", by decide⟩], by decide⟩⟩, 0⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 1 }
private def localId (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "inputs.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional condition span left span right⟩
private def base : LocalInputs :=
  LocalInputs.empty.bindFresh owner "word" .word (.word Core.Word.zero) .word
private def inputs (choice : Bool) : LocalInputs :=
  ((base.bindFresh owner "right" .bool (.bool true) .bool).bindFresh
    owner "left" .bool (.bool false) .bool).bindFresh
    owner "cond" .bool (.bool choice) .bool
private def names : LocalNameTable :=
  [("cond", localId 3), ("left", localId 2), ("right", localId 1), ("word", localId 0)]
private def context : Resolved.Context :=
  [(localId 3, .bool), (localId 2, .bool), (localId 1, .bool), (localId 0, .word)]
private def source : Syntax.Expr := branch (ref "cond") (ref "left") (ref "right")
private def resolved : Resolved.Expr :=
  .ifE (.var (localId 3)) (.var (localId 2)) (.var (localId 1))
private def core : Core.Expr := .ifE (.var 0) (.var 1) (.var 2)
private def original : LocalInputs :=
  LocalInputs.empty.bindFresh owner "item" .bool (.bool false) .bool
private def shadowed : LocalInputs := original.bindFresh owner "item" .unit .unit .unit
private def distinct : LocalInputs := original.bindFresh owner "other" .unit .unit .unit

theorem empty_and_owner_relative_fresh_indices (choice : Bool) :
    LocalInputs.empty.ids = [] ∧ base.ids = [localId 0] ∧
    (inputs choice).ids = [localId 3, localId 2, localId 1, localId 0] ∧
    (base.bindFresh otherOwner "external" .unit .unit .unit).ids =
      [⟨otherOwner, 0⟩, localId 0] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem generated_inputs_have_aligned_typed_projections (choice : Bool) :
    (inputs choice).ids.Nodup ∧
    Resolved.LocalScope.ids (inputs choice).environment =
      Resolved.LocalScope.ids (inputs choice).context ∧
    Core.EnvironmentHasTypes (Resolved.LocalScope.values (inputs choice).environment)
      (Resolved.LocalScope.values (inputs choice).context) :=
  ⟨(inputs choice).ids_nodup, (inputs choice).sameIds, (inputs choice).environmentTyped⟩

private theorem checked_conditional (choice : Bool) :
    (inputs choice).check? source = some (core, .bool) := by
  change elaborateLocalExpression? names context source = some (core, .bool)
  apply elaborateLocalExpression?_complete (resolved := resolved)
  · exact .conditional (.identifier .head) (.identifier (.tail (by decide) .head))
      (.identifier (.tail (by decide) (.tail (by decide) .head)))
  · exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))
  · exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))

theorem fresh_same_name_shadows_type_and_value (store : Core.Store) :
    original.check? (ref "item") = some (.var 0, .bool) ∧
    shadowed.ids = [localId 1, localId 0] ∧
    shadowed.check? (ref "item") = some (.var 0, .unit) ∧
    original.run? 1 (ref "item") store = some (.bool, .done (.bool false) store) ∧
    shadowed.run? 1 (ref "item") store = some (.unit, .done .unit store) := by
  have oldChecked : original.check? (ref "item") = some (.var 0, .bool) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  have newChecked : shadowed.check? (ref "item") = some (.var 0, .unit) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  refine ⟨oldChecked, rfl, newChecked, ?_, ?_⟩
  · rw [LocalInputs.run?, oldChecked]; rfl
  · rw [LocalInputs.run?, newChecked]; rfl

theorem different_name_keeps_the_existing_identity_and_value (store : Core.Store) :
    ResolvesLocalExpression distinct.names (ref "item") (.var (localId 0)) ∧
    distinct.check? (ref "item") = some (.var 1, .bool) ∧
    distinct.run? 1 (ref "item") store = some (.bool, .done (.bool false) store) := by
  have resolution : ResolvesLocalExpression distinct.names (ref "item") (.var (localId 0)) :=
    .identifier (.tail (by decide) .head)
  have checked : distinct.check? (ref "item") = some (.var 1, .bool) :=
    elaborateLocalExpression?_complete resolution (.var (.tail (by decide) .head))
      (.var (.tail (by decide) .head))
  refine ⟨resolution, checked, ?_⟩
  rw [LocalInputs.run?, checked]
  rfl

/-- Insufficient fuel is a present result retaining the actual checked state,
not the absence used for failed checking. Both Boolean choices complete at four. -/
theorem conditional_check_and_present_execution_boundary (choice : Bool) (store : Core.Store) :
    (inputs choice).check? source = some (core, .bool) ∧
    (inputs choice).run? 0 source store = some (.bool, .outOfFuel
      (Core.State.initial core (Resolved.LocalScope.values (inputs choice).environment) store)) ∧
    (inputs choice).run? 3 source store = some (.bool, .outOfFuel
      (Core.State.initial (.var (if choice then 1 else 2))
        (Resolved.LocalScope.values (inputs choice).environment) store)) ∧
    ∀ extra, (inputs choice).run? (extra + 4) source store =
      some (.bool, .done (.bool (!choice)) store) := by
  refine ⟨checked_conditional choice, ?_, ?_, ?_⟩
  · rw [LocalInputs.run?, checked_conditional]; rfl
  · rw [LocalInputs.run?, checked_conditional]
    cases choice <;> rfl
  · intro extra
    rw [LocalInputs.run?, checked_conditional]
    change some (Core.Ty.bool, Core.runStateful (extra + 4) (Core.State.initial core
      [.bool choice, .bool false, .bool true, .word Core.Word.zero] store)) = _
    cases choice <;> simp [Core.runStateful, Core.State.initial, Core.advance, core]

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .string "7"⟩⟩
private def wordCondition : Syntax.Expr := branch (ref "word") (ref "left") (ref "right")
private def badForms : List Syntax.Expr := [ref "missing", unsupported, wordCondition]

private theorem bad_check (bad : Syntax.Expr) (member : bad ∈ badForms) :
    (inputs true).check? bad = none := by
  change elaborateLocalExpression? names context bad = none
  simp only [badForms, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    unsupported, interpretWordLiteral?, numericLiteralValue?,
    wordCondition, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  intro type inferred
  cases Core.infer_sound inferred with
  | ifE condition _ _ => cases condition with | var found => cases found

theorem failed_checks_are_absent_runs_at_every_fuel (fuel : Nat) (store : Core.Store) :
    ∀ bad ∈ badForms, (inputs true).check? bad = none ∧
      (inputs true).run? fuel bad store = none ∧
      ((inputs true).run? fuel bad store = none ↔ (inputs true).check? bad = none) := by
  intro bad member
  have checked := bad_check bad member
  exact ⟨checked, (LocalInputs.run?_eq_none_iff fuel store).mpr checked,
    LocalInputs.run?_eq_none_iff fuel store⟩

private def unselectedMissing : Syntax.Expr := branch (ref "cond") (ref "left") (ref "missing")

/-- Raw selected-branch evaluation cannot bypass whole-expression checking. -/
theorem raw_evaluation_does_not_make_an_unchecked_run (fuel : Nat) (store : Core.Store) :
    LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      unselectedMissing (.bool false) store ∧
    (inputs true).check? unselectedMissing = none ∧
    (inputs true).run? fuel unselectedMissing store = none := by
  have checked : (inputs true).check? unselectedMissing = none := by
    change elaborateLocalExpression? names context unselectedMissing = none
    simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?,
      names, unselectedMissing, branch, ref]
  refine ⟨?_, checked, (LocalInputs.run?_eq_none_iff fuel store).mpr checked⟩
  exact .ifTrue (.identifier .head .head)
    (.identifier (.tail (by decide) .head) (.tail (by decide) .head))

theorem repeated_identity_cannot_construct_inputs (binding : TypedLocalBinding) :
    ¬ ∃ supplied : LocalInputs, supplied.bindings = [binding, binding] := by
  rintro ⟨supplied, rows⟩
  have unique := supplied.ids_nodup
  simp [rows] at unique

end Tests.FrontendLocalInputs
