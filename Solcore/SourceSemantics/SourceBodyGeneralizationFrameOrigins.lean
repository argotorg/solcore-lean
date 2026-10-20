import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedForContracts
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceTyping
import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

/-! Each active flexible variable comes from an actual outer initialized
binding. Acyclic occurrence paths and unique local identities distinguish
that binding from the initializer currently being checked. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyGeneralizationFrameOrigins
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness

private theorem flatMap_sublist {α β : Type} (values : List α) (f g : α → List β)
    (each : ∀ value, List.Sublist (f value) (g value)) : List.Sublist (values.flatMap f) (values.flatMap g) := by
  induction values with
  | nil => exact .refl _
  | cons head rest ih => exact (each head).append ih

private theorem forItem_ids (item : ForItemForm) :
    List.Sublist ((forItemInitializedLetBindings item).map fun binding => binding.binder.id)
      (forItemDefinedLocalIds item) := by
  cases item <;> try exact .refl _
  rename_i binder initializer
  cases initializer <;> simp [forItemInitializedLetBindings, forItemDefinedLocalIds]

private theorem form_ids (form : StatementForm) :
    List.Sublist ((statementInitializedLetBindings form).map fun binding => binding.binder.id)
      (statementDefinedLocalIds form) := by
  cases form <;> try exact List.nil_sublist _
  case letDecl binder initializer =>
    cases initializer <;> simp [statementInitializedLetBindings, statementDefinedLocalIds]
  case forLoop initial condition post body =>
    simp only [statementInitializedLetBindings, statementDefinedLocalIds, List.map_append, List.map_flatMap]
    exact (flatMap_sublist initial _ _ forItem_ids).append (flatMap_sublist post _ _ forItem_ids)

private theorem initialized_ids (source : TypedSource) :
    List.Sublist ((initializedLetBindings source).map fun binding => binding.binder.id)
      (definedLocalIds source) := by
  unfold initializedLetBindings definedLocalIds
  rw [List.map_flatMap]
  apply List.sublist_append_of_sublist_right
  apply flatMap_sublist
  intro node
  cases node with
  | expression expression => exact List.nil_sublist _
  | statement statement => exact form_ids statement.form


variable {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
  {selected : BodySelection compiled row fuel}
  {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

/-- Recover a raw outer binding from the finalized context and the real
strict containment relation of the current initializer. -/
theorem of_nested {current : InitializedLetBinding}
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (retained : FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution current ∈
      initializedLetBindings selected.body.finalized.typedSource)
    (nested : ∀ outer ∈ frames,
      Descends selected.body.finalized.typedSource outer.initializer current.initializer)
    {metavariable : TypeVarId} (occurs : metavariable ∈ target.typeVariables) :
    ∃ other ∈ initializedLetBindings (evidenceSource selected),
      other.binder ≠ current.binder ∧ metavariable ∈ other.binder.scheme.quantified := by
  rw [actual.variables_eq] at occurs
  obtain ⟨frame, frameMember, quantified⟩ := List.mem_flatMap.mp occurs
  have frameRetained := actual.retained frame frameMember
  have rawRetained := frameRetained
  rw [selected.body.resources.source_eq,
    FlexibleSubstitution.initializedLetBindings_applySubstitution] at rawRetained
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp rawRetained
  refine ⟨original, originalMember, ?_, ?_⟩
  · intro equalBinder
    have unique := (initialized_ids selected.body.finalized.typedSource).nodup
      selected.body.resources.local_identity_ownership.unique
    have ids : frame.binder.id =
        (FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution current).binder.id := by
      rw [← same]
      change original.binder.id = current.binder.id
      exact congrArg TypedBinder.id equalBinder
    have equalBinding := eq_of_mem_of_nodup_map unique frameRetained retained ids
    have path := nested frame frameMember
    rw [equalBinding] at path
    exact selected.body.resources.graph_closed.acyclic _ path
  · rw [← same] at quantified
    exact quantified

/-- Statement scopes are recovered from the same accepted let occurrence
and the context used by its existing typing proof. -/
theorem statement {source : Syntax.Statement} {expectedReturn : Ty}
    (occurrence : BodyInitializerOccurrence selected source)
    (boundary : StatementBoundary selected (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target)
    {metavariable : TypeVarId} (occurs : metavariable ∈ target.typeVariables) :
    ∃ other ∈ initializedLetBindings (evidenceSource selected),
      other.binder ≠ occurrence.receipt.binding.1 ∧ metavariable ∈ other.binder.scheme.quantified := by
  have idEq : occurrence.result.id = occurrence.entry.allocateStatementId.1 :=
    congrArg Detail.StatementResult.id occurrence.receipt.completed
  have entered := occurrence.enter (RecursiveExpressionInvariant.ofStatement boundary.invariant)
    boundary.actual (idEq ▸ boundary.actualCovered)
  have currentMember : occurrence.initializerBinding ∈ frames ++ [occurrence.initializerBinding] := by simp
  have retained := entered.2.1.retained occurrence.initializerBinding currentMember
  have nested := (List.pairwise_append.mp entered.2.1.nested).2.2
  exact of_nested (current := ⟨occurrence.receipt.binding.1, .expression occurrence.receipt.value.id⟩)
    boundary.actual retained
    (fun outer member => nested outer member occurrence.initializerBinding (by simp)) occurs

/-- Header scopes use the actual initialized item and its retained strict
containment relation, including initialization inside loop headers. -/
theorem header {childFuel : Nat} {inferenceContext : SourceInference.Context}
    {item : Syntax.ForItem} {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target)
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel inferenceContext item initial (inferred, final))
    {metavariable : TypeVarId} (occurs : metavariable ∈ target.typeVariables) :
    ∃ other ∈ initializedLetBindings (evidenceSource selected),
      other.binder ≠ receipt.binding.1 ∧ metavariable ∈ other.binder.scheme.quantified := by
  let binding : InitializedLetBinding := ⟨receipt.binding.1, .expression receipt.value.id⟩
  have member : binding ∈ forItemInitializedLetBindings inferred := by
    have itemEq : inferred = .letDecl receipt.binding.1 (some receipt.value.id) := receipt.recorded
    rw [itemEq]
    exact List.mem_singleton_self _
  have nested := boundary.actualBindings binding member
  exact of_nested (current := binding) boundary.actual nested.1 nested.2 occurs

end Solcore.SourceSemantics.SourceBodyGeneralizationFrameOrigins
