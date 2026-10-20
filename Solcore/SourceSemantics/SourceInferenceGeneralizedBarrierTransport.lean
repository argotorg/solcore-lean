import Solcore.SourceSemantics.SourceInferenceUnannotatedLetCertificate

/-! Exact generalization under residual substitutions. The ordered frontier
is derived from retained quantifiers and the images of actual blocked variables;
replacement types may retain flexible variables. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem
namespace GeneralizedBarrierTransport

private def mergeVariables (left right : List TypeVarId) : List TypeVarId :=
  right.foldl (fun variables metavariable =>
    if metavariable ∈ variables then variables else variables ++ [metavariable]) left

private theorem filter_mergeVariables (keep : TypeVarId → Bool)
    (left right : List TypeVarId) :
    (mergeVariables left right).filter keep =
      mergeVariables (left.filter keep) (right.filter keep) := by
  induction right generalizing left with
  | nil => simp [mergeVariables]
  | cons head tail ih =>
    change (mergeVariables (if head ∈ left then left else left ++ [head]) tail).filter keep =
      mergeVariables (left.filter keep) ((head :: tail).filter keep)
    rw [ih]
    by_cases kept : keep head
    · by_cases present : head ∈ left
      · simp [mergeVariables, kept, present, List.mem_filter.mpr ⟨present, kept⟩]
      · have absent : head ∉ left.filter keep := by simp [present]
        simp [mergeVariables, kept, present, absent, List.filter_append]
    · by_cases present : head ∈ left
      · simp [mergeVariables, kept, present]
      · simp [mergeVariables, kept, present, List.filter_append]

/-- A pointwise metavariable-image argument preserves the stable order of the
surviving variables, including when substitutions introduce residual variables. -/
private theorem filtered_apply
    (outer : Substitution) (before after : TypeVarId → Bool) (type : Ty)
    (images : ∀ metavariable ∈ type.freeVariables,
      (outer.apply (.variable metavariable)).freeVariables.filter after =
        ([metavariable].filter before)) :
    (outer.apply type).freeVariables.filter after = type.freeVariables.filter before := by
  induction type with
  | «variable» metavariable => exact images metavariable (by simp [Ty.freeVariables])
  | parameter _ => rfl
  | constructor _ => rfl
  | error => rfl
  | proxy _ ih => exact ih images
  | comptime _ ih => exact ih images
  | application left right leftIH rightIH
  | function left right leftIH rightIH
  | product left right leftIH rightIH
  | mapping left right leftIH rightIH =>
    change (mergeVariables (outer.apply left).freeVariables (outer.apply right).freeVariables).filter after =
      (mergeVariables left.freeVariables right.freeVariables).filter before
    rw [filter_mergeVariables, filter_mergeVariables]
    congr 1
    · apply leftIH
      intro metavariable member
      apply images metavariable
      simp_all only [Ty.mem_freeVariables_application_iff, Ty.mem_freeVariables_function_iff,
        Ty.mem_freeVariables_product_iff, Ty.mem_freeVariables_mapping_iff, true_or]
    · apply rightIH
      intro metavariable member
      apply images metavariable
      simp_all only [Ty.mem_freeVariables_application_iff, Ty.mem_freeVariables_function_iff,
        Ty.mem_freeVariables_product_iff, Ty.mem_freeVariables_mapping_iff, or_true]

end GeneralizedBarrierTransport

/-- The actual generalized scheme and final capture check reduce exact
frontier transport to two provenance facts: images of old blockers stay
blocked, and this binder's private quantifiers do not enter the final barrier. -/
theorem generalizationBarrierTransport_of_blockedImages
    {state : State} {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {outer : Substitution} {target : SourceSemantics.Context}
    {binder : TypedBinder} {exemptRequirements : List RequirementId}
    (schemeEq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart valueType).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (blockedImages : ∀ metavariable ∈ valueType.freeVariables,
      metavariable ∈ Detail.generalizeValueBlockedVariables state locals requirementStart →
      ∀ replacement ∈ (outer.apply (.variable metavariable)).freeVariables,
        replacement ∈ GeneralizationBlockedVariablesExcept target exemptRequirements)
    (privateQuantifiers : ∀ metavariable ∈ binder.scheme.quantified,
      metavariable ∉ GeneralizationBlockedVariablesExcept target exemptRequirements) :
    GeneralizationBarrierTransport state locals requirementStart valueType
      outer target exemptRequirements := by
  apply GeneralizedBarrierTransport.filtered_apply
  intro metavariable occurs
  by_cases blocked : metavariable ∈ Detail.generalizeValueBlockedVariables state locals requirementStart
  · have empty : (outer.apply (.variable metavariable)).freeVariables.filter
        (fun replacement => !(GeneralizationBlockedVariablesExcept target exemptRequirements).contains replacement) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro replacement member
      simp [blockedImages metavariable occurs blocked replacement member]
    simpa [blocked] using empty
  · have quantified : metavariable ∈ binder.scheme.quantified := by
      rw [schemeEq, Detail.generalizeValue_scheme_quantified]
      exact List.mem_filter.mpr ⟨occurs, by simp [blocked]⟩
    have found : outer.lookup? metavariable = none :=
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr
        (noCapture.quantified_fresh metavariable quantified)
    simp [Substitution.apply, found, Ty.freeVariables, blocked,
      privateQuantifiers metavariable quantified]

end Solcore.SourceSemantics.SourceInferenceSoundness
