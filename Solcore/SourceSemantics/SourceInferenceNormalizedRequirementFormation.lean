import Solcore.SourceSemantics.SourceInferenceLocalReadRequirementFormation

/-! Retained local-read issuances preserve the prior binder's normalized formation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

private theorem row_eq_of_unique_ids
    {rows : List Requirement}
    (unique : (rows.map (fun row => row.id.index)).Nodup)
    {left right : Requirement} (leftMember : left ∈ rows)
    (rightMember : right ∈ rows) (same : left.id = right.id) : left = right := by
  induction rows generalizing left right with
  | nil => simp at leftMember
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exact False.elim (unique.1 (List.mem_map.mpr
            ⟨right, rightMember, congrArg RequirementId.index same.symm⟩))
      · rcases rightMember with rfl | rightMember
        · exact False.elim (unique.1 (List.mem_map.mpr
            ⟨left, leftMember, congrArg RequirementId.index same⟩))
        · exact induction unique.2 leftMember rightMember same

/-- Actual ledger identities select the producer's exact predicate before
normalization; later ledger membership alone does not supply its formation. -/
theorem retained_normalized_issued_row_formed
    {context : SourceSemantics.Context} {state : State} {outer : Substitution}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (wellFormed : state.RequirementsWellFormed)
    (correspondence : RequirementPredicatesCorrespond state.requirements predicates ids)
    (formed : ∀ predicate ∈ predicates,
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate))
    {row : Requirement} (member : row ∈ state.requirements) (selected : row.id ∈ ids) :
    PredicateAdmissible context (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have origin : ∃ predicate, ({ id := row.id, predicate } : Requirement) ∈ state.requirements ∧
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) := by
    induction correspondence with
    | nil => simp at selected
    | @cons predicate id predicates ids head _ ih =>
      rcases List.mem_cons.mp selected with rfl | tail
      · exact ⟨predicate, head, formed predicate (by simp)⟩
      · exact ih (fun predicate member => formed predicate (by simp [member])) tail
  obtain ⟨predicate, issuedMember, predicateFormed⟩ := origin
  have unique : (state.requirements.map (fun row => row.id.index)).Nodup := by
    rw [show state.requirements.map (fun row => row.id.index) =
      List.range state.nextRequirement from wellFormed]
    exact List.nodup_range
  have same := row_eq_of_unique_ids unique member issuedMember rfl
  exact (congrArg Requirement.predicate same).symm ▸ predicateFormed

/-- An actual earlier lookup contributes normalized formation for the exact
retained row of its real batch, using that earlier binder's certificate. -/
theorem retained_local_read_row_formed
    (lookup : LocalReadEvents.Lookup)
    {outer : Substitution} {context : SourceSemantics.Context} {retained : State}
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context outer)
    (formation : LocalSchemeRequirementsWellFormed context (lookup.binder.applySubstitution outer))
    (scheme : SchemeWellFormed context (lookup.binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer lookup.binder)
    (continuation : outer.SemanticallyExtends lookup.advanced.inference.substitution)
    (included : lookup.result.2.requirements ⊆ retained.requirements)
    (wellFormed : retained.RequirementsWellFormed)
    {row : Requirement} (member : row ∈ retained.requirements)
    (selected : row.id ∈ lookup.batch.1) :
    PredicateAdmissible context (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have issuance := local_read_issuance lookup binders residual range formation scheme noCapture continuation
  exact retained_normalized_issued_row_formed wellFormed (issuance.1.mono included)
    issuance.2 member selected

/-- Normalized producer formation connects directly to the existing let
certificate. Actual continuation absorbs the ready substitution and actual
no-capture removes the quantifier restriction. -/
theorem retained_formation_of_normalized_issuances
    {ready : State} {binder : TypedBinder} {outer : Substitution}
    {target : SourceSemantics.Context}
    (continuation : outer.SemanticallyExtends ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (issued : ∀ row ∈ ready.requirements, row.id ∈ localSchemeTemplateIds binder →
      PredicateAdmissible (localSchemeInitializerContext target (binder.applySubstitution outer))
        (TypedTraitResolution.applySubstitution outer row.predicate)) :
    RetainedRequirementPredicateFormationAt ready binder outer target := by
  intro row member selected
  rw [retained_predicate_normalization continuation noCapture]
  exact issued row member selected

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
