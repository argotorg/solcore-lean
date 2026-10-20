import Solcore.SourceSemantics.SourceInferenceNormalizedAtomFormation
import Solcore.SourceSemantics.SourceInferenceLocalReadRequirementFormation

/-! The real local lookup reuses the earlier binder's formation and exact
fresh instantiation, then includes its actual expected-fitting obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

private theorem batch_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact Or.inl member
  | cons predicate predicates ih =>
    rcases ih (state.addRequirementWithId predicate).2 member with old | issued
    · rcases List.mem_append.mp old with old | new
      · exact .inl old
      · simp only [List.mem_singleton] at new
        subst row
        exact .inr (by simp)
    · exact .inr (by simp [issued])

/-- This is only scheme instantiation and structural type formation. It does
not require expression typing or evidence entailment for the current use. -/
theorem local_instantiated_type_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution} {binder : TypedBinder}
    (binders : TypeParameterBindersWellFormed semantic)
    (residual : semantic.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible semantic outer)
    (scheme : SchemeWellFormed semantic (binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder) (next : Nat) :
    TypeAdmissible semantic (outer.apply (binder.scheme.instantiateWithSubstitution next).body) := by
  let instantiated := binder.scheme.instantiateWithSubstitution next
  have unique : binder.scheme.quantified.Nodup := by simpa using scheme.quantified_nodup
  have exactInner : ExactSubstitution instantiated.substitution binder.scheme.quantified := {
    variables_nodup := unique
    domain_permutation := binder.scheme.instantiateWithSubstitution_substitution_domain_permutation next unique }
  have restricted : outer.without binder.scheme.quantified = outer :=
    FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain outer binder.scheme.quantified
      noCapture.quantified_fresh
  have composedRange := FlexibleSubstitution.SubstitutionRangeAdmissible.mapRange_instantiateWithSubstitution
    binder.scheme next binders residual range
  have instantiatedValid : SchemeInstantiatesAt semantic (binder.applySubstitution outer).scheme
      (outer.apply instantiated.body) := by
    refine .intro scheme (FlexibleSubstitution.Substitution.mapRange outer instantiated.substitution)
      (FlexibleSubstitution.Substitution.ExactSubstitution.mapRange outer exactInner) composedRange ?_
    change (FlexibleSubstitution.Substitution.mapRange outer instantiated.substitution).apply
      (binder.applySubstitution outer).scheme.body = outer.apply instantiated.body
    rw [FlexibleSubstitution.applyTypedBinder_scheme]
    change (FlexibleSubstitution.Substitution.mapRange outer instantiated.substitution).apply
      ((outer.without binder.scheme.quantified).apply binder.scheme.body) = outer.apply instantiated.body
    rw [restricted]
    exact (FlexibleSubstitution.Ty.applyFlexible_compose_of_rangeAvoidsVariablesOn outer
      instantiated.substitution exactInner noCapture.quantified_fresh noCapture.body_range).symm
  exact instantiatedValid.type_admissible

/-- The accepted local-reference branch produces its exact predicate batch
and then performs ordinary expected fitting. Earlier binder formation is the
only local scheme input; current-expression typing is not assumed. -/
theorem inferExprFuel_local_normalized_formation
    (lookup : LocalReadEvents.Lookup) {semantic : SourceSemantics.Context} {outer : Substitution}
    (formation : FormationContext semantic lookup.context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (earlierRequirements : LocalSchemeRequirementsWellFormed semantic (lookup.binder.applySubstitution outer))
    (earlierScheme : SchemeWellFormed semantic (lookup.binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer lookup.binder)
    (beforeContinuation : outer.SemanticallyExtends lookup.advanced.inference.substitution)
    (afterContinuation : outer.SemanticallyExtends lookup.result.2.inference.substitution)
    (expectedFormed : ∀ type ∈ lookup.expected, TypeAdmissible semantic (outer.apply type)) :
    TypeAdmissible semantic (outer.apply lookup.result.1.type) ∧
      ∀ row ∈ lookup.result.2.requirements, row ∉ lookup.initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have bodyFormed := local_instantiated_type_normalized binders formation.residual formation.range
    earlierScheme noCapture lookup.allocated.inference.next
  have resolvedFormed : TypeAdmissible semantic
      (outer.apply (lookup.advanced.resolve
        (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).body)) :=
    (beforeContinuation _).symm ▸ bodyFormed
  have predicatesFormed := local_read_normalized_predicates lookup binders formation.residual formation.range
    earlierRequirements earlierScheme noCapture beforeContinuation
  have recorded := recordExpressionWithExpected_normalized_formation formation afterContinuation
    resolvedFormed expectedFormed lookup.recorded
  refine ⟨recorded.1, new_normalized_requirements_trans (middle := lookup.batch.2) ?_ recorded.2⟩
  intro row member fresh
  rcases batch_origin lookup.advanced lookup.predicates member with old | issued
  · have present : row ∈ lookup.allocated.requirements := old
    have allocatedEq : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
      (congrArg Prod.snd lookup.allocation).symm
    rw [allocatedEq] at present
    exact (fresh present).elim
  · exact predicatesFormed row.predicate issued

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
