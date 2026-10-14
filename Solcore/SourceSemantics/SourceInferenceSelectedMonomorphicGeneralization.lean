import Solcore.SourceSemantics.SourceInferenceSelectedLocalSchemePrivacy
import Solcore.SourceSemantics.SourceInferenceUnannotatedLetCertificate

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem
namespace MonomorphicGeneralization

/-- An occurrence in a replacement survives at every occurrence of its source
 variable. No restriction on residual variables or substitution ranges is used. -/
theorem replacement_occurs (substitution : Substitution) (type : Ty)
    {original replacement : TypeVarId} (occurs : original ∈ type.freeVariables)
    (replaced : replacement ∈ (substitution.apply (.variable original)).freeVariables) :
    replacement ∈ (substitution.apply type).freeVariables := by
  induction type with
  | «variable» metavariable =>
    have same : original = metavariable := by simpa [Ty.freeVariables] using occurs
    simpa only [same] using replaced
  | parameter parameter => simp [Ty.freeVariables] at occurs
  | constructor constructor => simp [Ty.freeVariables] at occurs
  | application left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_application_iff _ _ _).mp occurs with left | right
    · exact (Ty.mem_freeVariables_application_iff _ _ _).mpr (.inl (leftIH left))
    · exact (Ty.mem_freeVariables_application_iff _ _ _).mpr (.inr (rightIH right))
  | function left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_function_iff _ _ _).mp occurs with left | right
    · exact (Ty.mem_freeVariables_function_iff _ _ _).mpr (.inl (leftIH left))
    · exact (Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr (rightIH right))
  | product left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_product_iff _ _ _).mp occurs with left | right
    · exact (Ty.mem_freeVariables_product_iff _ _ _).mpr (.inl (leftIH left))
    · exact (Ty.mem_freeVariables_product_iff _ _ _).mpr (.inr (rightIH right))
  | mapping left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_mapping_iff _ _ _).mp occurs with left | right
    · exact (Ty.mem_freeVariables_mapping_iff _ _ _).mpr (.inl (leftIH left))
    · exact (Ty.mem_freeVariables_mapping_iff _ _ _).mpr (.inr (rightIH right))
  | proxy inner ih => exact ih occurs
  | comptime inner ih => exact ih occurs
  | error => simp [Ty.freeVariables] at occurs

theorem predicate_replacement_occurs (substitution : Substitution) (predicate : ProgramPredicate)
    {original replacement : TypeVarId}
    (occurs : original ∈ TypedTraitResolution.predicateVariables predicate)
    (replaced : replacement ∈ (substitution.apply (.variable original)).freeVariables) :
    replacement ∈ TypedTraitResolution.predicateVariables
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with subject | ⟨argument, member, occurs⟩
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr
      (.inl (replacement_occurs substitution predicate.subject subject replaced))
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr
      (.inr ⟨substitution.apply argument, List.mem_map.mpr ⟨argument, member, rfl⟩,
        replacement_occurs substitution argument occurs replaced⟩)

private theorem solved_row {context : Frontend.SourceInference.Context} {state : State}
    {requirements : List Requirement} {solved : List SolvedRequirement}
    (rows : Forall₂ (fun requirement row => row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate ∧
      Detail.solveRequirementEvidence context state requirement = .ok row.evidence) requirements solved)
    {requirement : Requirement} (member : requirement ∈ requirements) :
    ∃ row ∈ solved, row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction rows with
  | nil => cases member
  | @cons head row tail rows relation rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨row, List.mem_cons_self, relation.2.1⟩
    · obtain ⟨selected, present, same⟩ := ih member
      exact ⟨selected, List.mem_cons_of_mem _ present, same⟩

/-- A monomorphic generalization needs only forward preservation of blockers.
All earlier rows are still in the actual solved ledger, and the final lexical
context retains the substituted old schemes. Later requirements cannot
invalidate this case. -/
theorem final_variables_blocked
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {evidenceState state : State} {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {target : SourceSemantics.Context} {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    (monomorphic : (Detail.generalizeValue state locals requirementStart valueType).scheme.quantified = [])
    (localMonomorphic : ∀ entry ∈ locals, entry.2.quantified = [])
    (localPresent : ∀ entry ∈ locals, ∃ id,
      (id, entry.2.apply finalized.substitution) ∈ target.locals)
    (requirements : state.requirements ⊆ evidenceState.requirements)
    (extension : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (solvedEq : target.solvedRequirements = finalized.solvedRequirements) :
    ∀ replacement ∈ (finalized.substitution.apply valueType).freeVariables,
      replacement ∈ GeneralizationBlockedVariablesExcept target [] := by
  intro replacement occurs
  obtain ⟨original, originalOccurs, replaced⟩ :=
    ProtectedVariables.apply_variable_origin finalized.substitution valueType replacement occurs
  have blocked : original ∈ Detail.generalizeValueBlockedVariables state locals requirementStart := by
    by_cases blocked : original ∈ Detail.generalizeValueBlockedVariables state locals requirementStart
    · exact blocked
    apply False.elim
    have quantified : original ∈ (Detail.generalizeValue state locals requirementStart valueType).scheme.quantified := by
      rw [Detail.generalizeValue_scheme_quantified]
      exact List.mem_filter.mpr ⟨originalOccurs, by simp only [List.contains_eq_mem, blocked, decide_false, Bool.not_false]⟩
    rw [monomorphic] at quantified
    cases quantified
  rcases (Detail.mem_generalizeValueBlockedVariables_iff _ _ _ _).mp blocked with
    ⟨entry, member, variableMember⟩ | ⟨requirement, member, variableMember⟩
  · obtain ⟨id, present⟩ := localPresent entry member
    have mono := localMonomorphic entry member
    have bodyMember : original ∈ entry.2.body.freeVariables := by
      exact (List.mem_filter.mp variableMember).1
    have finalMember : replacement ∈ (entry.2.apply finalized.substitution).freeVariables := by
      simpa [Scheme.freeVariables, Scheme.apply, mono, Substitution.without] using
        replacement_occurs finalized.substitution entry.2.body bodyMember replaced
    apply List.mem_append.mpr
    exact .inl (List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨(id, entry.2.apply finalized.substitution), present, finalMember⟩)))
  · have inState : requirement ∈ state.requirements := by
      rcases (Detail.mem_generalizeValueBlockingRequirements_iff _ _ _).mp member with prior | ⟨introduced, _⟩
      · exact List.mem_of_mem_take prior
      · exact List.mem_of_mem_drop introduced
    have inFinal : requirement ∈ resources.finalState.requirements := by
      rw [resources.requirements_eq]
      exact requirements inState
    obtain ⟨row, rowMember, predicateEq⟩ := solved_row (solveRequirements_corresponds resources.solve_success) inFinal
    have predicateMember := predicate_replacement_occurs finalized.substitution
      (Detail.applyPredicate state requirement.predicate) variableMember replaced
    rw [Detail.applyPredicate, TypedTraitResolution.applySubstitution_semanticallyExtends extension] at predicateMember
    have rowOccurs : replacement ∈ TypedTraitResolution.predicateVariables row.predicate := by
      rw [predicateEq, Detail.applyPredicate, ← resources.substitution_eq]
      exact predicateMember
    apply List.mem_append.mpr
    apply Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨row, ?_, rowOccurs⟩
    exact List.mem_filter.mpr ⟨by simpa only [solvedEq] using rowMember, rfl⟩

end MonomorphicGeneralization

/-- Actual monomorphic generalization remains exact after finalization even
when its body retains flexible variables. The old lexical environment and
original solved ledger supply every remaining blocker. -/
theorem unannotatedInitializedLetCertificate_of_finalMonomorphic
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {evidenceState state final : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {source : TypedSource} {target : SourceSemantics.Context}
    {locals : Environment} {requirementStart : Nat} {valueType : Ty}
    {generalized : Detail.GeneralizedValue} {name : Syntax.Identifier}
    {binder : TypedBinder} {initializer : ExpressionId}
    (generalizedEq : generalized = Detail.generalizeValue state locals requirementStart valueType)
    (allocated : (state.withLocals locals).allocateBinder name.value generalized.scheme
      (some name.span) false generalized.requirements = (binder, final))
    (monomorphic : (binder.applySubstitution finalized.substitution).scheme.quantified = [])
    (localMonomorphic : ∀ entry ∈ locals, entry.2.quantified = [])
    (localPresent : ∀ entry ∈ locals, ∃ id,
      (id, entry.2.apply finalized.substitution) ∈ target.locals)
    (requirements : state.requirements ⊆ evidenceState.requirements)
    (extension : finalized.substitution.SemanticallyExtends state.inference.substitution)
    (solvedEq : target.solvedRequirements = finalized.solvedRequirements)
    (initializerType : ExpressionHasType (source.applySubstitution finalized.substitution)
      (localSchemeInitializerContext target (binder.applySubstitution finalized.substitution))
      initializer (binder.applySubstitution finalized.substitution).scheme.body) :
    UnannotatedInitializedLetCertificate source target finalized.substitution binder initializer := by
  have binderEq :
      ((state.withLocals locals).allocateBinder name.value generalized.scheme
        (some name.span) false generalized.requirements).1 = binder := congrArg Prod.fst allocated
  have rawMonomorphic : binder.scheme.quantified = [] := monomorphic
  have generalizedMonomorphic :
      (Detail.generalizeValue state locals requirementStart valueType).scheme.quantified = [] := by
    rw [← generalizedEq]
    rw [← binderEq] at rawMonomorphic
    exact rawMonomorphic
  have rawRequirements : binder.schemeRequirements = [] := by
    rw [← binderEq]
    change generalized.requirements = []
    rw [generalizedEq]
    exact Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
      state locals requirementStart valueType generalizedMonomorphic
  have rawBody : binder.scheme.body = valueType := by
    rw [← binderEq]
    change generalized.scheme.body = valueType
    rw [generalizedEq, Detail.generalizeValue_scheme_body]
  have finalBody : (binder.applySubstitution finalized.substitution).scheme.body =
      finalized.substitution.apply valueType := by
    simp only [TypedBinder.applySubstitution, Scheme.apply, rawMonomorphic]
    simp [Substitution.without, rawBody]
  have finalRequirements : (binder.applySubstitution finalized.substitution).schemeRequirements = [] := by
    simp [TypedBinder.applySubstitution, rawRequirements]
  have blocked := MonomorphicGeneralization.final_variables_blocked resources generalizedMonomorphic
    localMonomorphic localPresent requirements extension solvedEq
  exact {
    initializer_type := initializerType
    requirements_well_formed := LocalSchemeRequirementsWellFormed.empty target
      (binder.applySubstitution finalized.substitution) finalRequirements
    generalizes := by
      unfold SchemeGeneralizesExcept
      rw [monomorphic, finalBody]
      have templates : localSchemeTemplateIds (binder.applySubstitution finalized.substitution) = [] := by
        simp [localSchemeTemplateIds, rawRequirements]
      rw [templates]
      apply Eq.symm
      apply List.filter_eq_nil_iff.mpr
      intro metavariable member
      simp only [List.contains_eq_mem, blocked metavariable member, decide_true, Bool.not_true]
      decide
    quantified_fresh := by
      intro metavariable member
      rw [monomorphic] at member
      cases member
  }

end Solcore.SourceSemantics.SourceInferenceSoundness
