import Solcore.SourceSemantics.SourceInferenceCoercionTargetFormation
import Solcore.SourceSemantics.SourceInferenceNormalizedProducerFormation

/-! Actual coercion matching produces formed intermediate targets directly
under the selected finalizer's substitution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem

theorem coercion_rule_edge_target_normalized
    {context : SourceSemantics.Context} {trait : Resolved.DeclarationId} {source : Ty}
    {rule : ProgramImplRule} {edge : Detail.CoercionEdge} {outer : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (residual : context.residualTypeVariables = true)
    (outerRange : SubstitutionRangeAdmissible context outer)
    (member : rule ∈ context.signatures.implRules)
    (sourceFormed : TypeAdmissible context (outer.apply source))
    (accepted : Detail.coercionRuleEdge? trait source rule = some edge) :
    edge.source = source ∧ TypeAdmissible context (outer.apply edge.target) ∧
      edge.predicate = {trait, subject := source, arguments := [edge.target]} := by
  let goal : ProgramPredicate := {trait := .declaration trait, subject := source, arguments := [source]}
  have fresh := coercion_rule_fresh_head_types catalog sourceFormed.binders residual member goal
  dsimp only [goal] at fresh
  by_cases mismatch : (rule.head.trait != ProgramTraitId.declaration trait) = true
  · simp [Detail.coercionRuleEdge?, mismatch] at accepted
  · simp only [Detail.coercionRuleEdge?, mismatch] at accepted
    cases arguments : (TypedTraitResolution.freshenRuleFor rule
        {trait := .declaration trait, subject := source, arguments := [source]}).head.arguments with
    | nil => simp [arguments, bind, Option.bind] at accepted
    | cons target rest =>
      cases rest with
      | cons second tail => simp [arguments, bind, Option.bind] at accepted
      | nil =>
        simp only [arguments, bind, Option.bind] at accepted
        cases unified : Unification.unify [{
            left := (TypedTraitResolution.freshenRuleFor rule
              {trait := .declaration trait, subject := source, arguments := [source]}).head.subject,
            right := source}] with
        | error error => simp [unified, Except.toOption] at accepted
        | ok substitution =>
          simp only [unified, Except.toOption] at accepted
          by_cases blocked : substitution.domain.any source.freeVariables.contains = true
          · simp [blocked] at accepted
          · by_cases ground : Detail.isGroundCoercionTarget (substitution.apply target) = true
            · simp [blocked, ground] at accepted
              subst edge
              refine ⟨rfl, ?_, rfl⟩
              have disjoint : ∀ metavariable, metavariable ∈ substitution.domain →
                  metavariable ∉ source.freeVariables := by
                intro metavariable domain occurs
                exact blocked (List.any_eq_true.mpr
                  ⟨metavariable, domain, List.contains_iff_mem.mpr occurs⟩)
              have matched := UnificationFormation.matching_normalized_range_admissible
                fresh.1 sourceFormed unified disjoint
              have composedRange : SubstitutionRangeAdmissible context (outer.compose substitution) := by
                intro metavariable replacement member
                rcases List.mem_append.mp member with updated | outerMember
                · obtain ⟨⟨original, type⟩, originalMember, same⟩ := List.mem_map.mp updated
                  cases same
                  exact matched original type originalMember
                · exact outerRange metavariable replacement (List.mem_filter.mp outerMember).1
              have targetFormed := fresh.2 target (by rw [arguments]; simp)
              simpa only [Substitution.compose_apply] using
                type_applySubstitution_residual residual composedRange targetFormed
            · simp [blocked, ground] at accepted

theorem coercion_assumption_edge_target_normalized
    {context : SourceSemantics.Context} {inferenceContext : SourceInference.Context} {state : State}
    {trait : Resolved.DeclarationId}
    {source : Ty} {edge : Detail.CoercionEdge} {outer : Substitution}
    (residual : context.residualTypeVariables = true)
    (outerRange : SubstitutionRangeAdmissible context outer)
    (formed : ∀ predicate ∈ inferenceContext.assumptions, PredicateWellFormed context predicate)
    (member : edge ∈ Detail.assumptionCoercionEdges inferenceContext state trait source) :
    edge.source = source ∧ TypeAdmissible context (outer.apply edge.target) ∧
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer edge.predicate) := by
  have result := coercion_assumption_edge_target formed member
  exact ⟨result.1, type_applySubstitution_residual residual outerRange result.2.1,
    predicate_applySubstitution_residual residual outerRange result.2.2⟩

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
